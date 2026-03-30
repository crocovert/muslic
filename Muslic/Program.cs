// ============================================================
//  MUSLIC — Version optimisée et parallélisée
//  Intègre toutes les optimisations :
//    [OPT-1]  Cache des références imbriquées
//    [OPT-2]  Reset O(1) par génération (supprime la boucle de réinit)
//    [OPT-3]  Lazy deletion dans les buckets (supprime List.Remove O(n))
//    [OPT-4]  CultureInfo.InvariantCulture (parsing décimal unifié)
//    [OPT-5]  poleV2 stocké comme List<string>, sérialisé à la sortie
//    [OPT-6]  HashSet filtre précalculé hors boucle O-D
//    [OPT-7]  StringBuilder pour la construction des lignes de sortie
//    [OPT-8]  args.Length au lieu de args.Count()
//    [PAR-1]  DijkstraState isolé par thread (extrait l'état de link)
//    [PAR-2]  Parallel.ForEach par groupe d'origines
//    [PAR-3]  Channel<string> writer dédié aux I/O
//    [PAR-4]  Accumulation volau/boai/alij séquentielle post-parallèle
// ============================================================

using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Channels;
using System.Threading.Tasks;

namespace Muslic
{
    // ══════════════════════════════════════════════════════════════════════
    //  [OPT-4] Culture invariante — calculée une seule fois pour tout le
    //          programme, élimine les if/else sur NumberDecimalSeparator
    // ══════════════════════════════════════════════════════════════════════
    static class Formats
    {
        public static readonly CultureInfo Inv  = CultureInfo.InvariantCulture;
        public static readonly string[]    Sep  = { ";" };
        public static readonly string[]    SepPipe = { "|" };

        // Normalise le séparateur décimal vers '.' puis parse
        public static float ParseFloat(string s)
        {
            var normalized = s.Trim().Replace(',', '.');
            return float.TryParse(normalized, NumberStyles.Float, Inv, out float v) ? v : 0f;
        }

        public static int ParseInt(string s)
        {
            var normalized = s.Trim().Replace(',', '.').Split('.')[0];
            return int.TryParse(normalized, NumberStyles.Integer, Inv, out int v) ? v : 0;
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    //  PaireOD — représente une ligne de la matrice O-D
    // ══════════════════════════════════════════════════════════════════════
    public class PaireOD
    {
        public string p, q, libod;
        public float  od, horaire;
        public int    jour, sens, numod;
        public bool   a_params_specifiques;
        // Paramètres spécifiques à la paire (colonnes 7-24, optionnels)
        public Dictionary<string,float> cveh, cwait, cmap, cboa, coef_tmap,
                                        tboa, tboa_max, ctoll;
        public bool  sortie_chemins;
        public int   sortie_temps, algorithme;
        public float param_dijkstra, max_nb_buckets, pu;
        public string texte_filtre_sortie;
    }

    // ══════════════════════════════════════════════════════════════════════
    //  [PAR-1] DijkstraState — tout l'état mutable de l'algorithme,
    //          un objet par thread (ThreadLocal)
    //
    //  Champs extraits de link :
    //    cout, touche, pivot, turn_pivot, service, h,
    //    tatt, tatt1, tcor, tmap, tveh, ttoll, l, ncorr,
    //    pole, is_queue
    //    + delta / boai / alij par service
    //
    //  [OPT-5] poleV2 stocké comme List<string> (pas de concaténation
    //          dans la boucle chaude) → sérialisé en string à la sortie
    //
    //  [OPT-2] reset O(1) par génération
    //  [OPT-3] lazy deletion : is_queue[] + insertion sans suppression
    // ══════════════════════════════════════════════════════════════════════
    public class DijkstraState
    {
        public readonly int NbLinks;

        public float[]  cout;
        public float[]  h;
        public float[]  tatt, tatt1, tcor, tmap, tveh, ttoll, l, ncorr;
        public int[]    touche, pivot, turn_pivot, service;
        public string[] pole;
        public bool[]   is_queue;       // [OPT-3] flag lazy deletion
        public int[]    gen;            // [OPT-2] génération courante au moment de l'init

        // [OPT-5] poleV2 comme liste (pas de concaténation de strings)
        public List<string>[] poleV2List;

        // Delta/boai/alij par service — indexés [linkIdx][serviceIdx]
        public float[][] delta_service;
        public float[][] boai_service;
        public float[][] alij_service;

        // Buckets GGA
        public List<List<int>> gga_nq;
        public int id_bucket;

        // [OPT-2] Génération courante
        public int generation;

        // Compteur nb_pop (local au thread)
        public int nb_pop;

        public DijkstraState(int nbLinks, int nbBuckets)
        {
            NbLinks        = nbLinks;
            cout           = new float[nbLinks];
            h              = new float[nbLinks];
            tatt           = new float[nbLinks];
            tatt1          = new float[nbLinks];
            tcor           = new float[nbLinks];
            tmap           = new float[nbLinks];
            tveh           = new float[nbLinks];
            ttoll          = new float[nbLinks];
            l              = new float[nbLinks];
            ncorr          = new float[nbLinks];
            touche         = new int[nbLinks];
            pivot          = new int[nbLinks];
            turn_pivot     = new int[nbLinks];
            service        = new int[nbLinks];
            pole           = new string[nbLinks];
            is_queue       = new bool[nbLinks];
            gen            = new int[nbLinks];
            poleV2List     = new List<string>[nbLinks];
            delta_service  = new float[nbLinks][];
            boai_service   = new float[nbLinks][];
            alij_service   = new float[nbLinks][];

            Array.Fill(gen, -1); // force init au premier accès

            gga_nq = new List<List<int>>(nbBuckets);
            for (int b = 0; b < nbBuckets; b++)
                gga_nq.Add(new List<int>(64));
        }

        // [OPT-2] Reset O(1) : incrémenter la génération suffit
        public void Reset()
        {
            generation++;
            foreach (var b in gga_nq) b.Clear();
            id_bucket = 0;
            nb_pop    = 0;
        }

        // Init paresseuse d'un lien (appelée avant toute écriture)
        public void EnsureInit(int idx, int nbServices)
        {
            if (gen[idx] == generation) return;

            cout[idx]       = 1e38f;
            h[idx]          = 0f;
            tatt[idx]       = 0f; tatt1[idx] = 0f; tcor[idx] = 0f;
            tmap[idx]       = 0f; tveh[idx]  = 0f; ttoll[idx] = 0f;
            l[idx]          = 0f; ncorr[idx] = 0f;
            touche[idx]     = 0;
            pivot[idx]      = -1;
            turn_pivot[idx] = -1;
            service[idx]    = -1;
            pole[idx]       = "-1";
            is_queue[idx]   = false;

            // [OPT-5] réutiliser la liste si déjà allouée
            if (poleV2List[idx] == null)
                poleV2List[idx] = new List<string>(8);
            else
                poleV2List[idx].Clear();

            if (delta_service[idx] == null || delta_service[idx].Length < nbServices)
            {
                delta_service[idx] = new float[nbServices];
                boai_service[idx]  = new float[nbServices];
                alij_service[idx]  = new float[nbServices];
            }
            else
            {
                Array.Clear(delta_service[idx], 0, nbServices);
                Array.Clear(boai_service[idx],  0, nbServices);
                Array.Clear(alij_service[idx],  0, nbServices);
            }

            gen[idx] = generation;
        }

        public bool EstAtteint(int idx)
            => gen[idx] == generation && touche[idx] != 0;

        // [OPT-5] Sérialiser poleV2 uniquement à la sortie
        public string GetPoleV2String(int idx)
            => poleV2List[idx] == null ? "" : string.Join("|", poleV2List[idx]);

        // Copier poleV2 d'un lien vers un autre (dans la boucle chaude)
        public void CopyPoleV2(int dst, int src)
        {
            if (poleV2List[dst] == null) poleV2List[dst] = new List<string>(8);
            else poleV2List[dst].Clear();
            if (poleV2List[src] != null)
                poleV2List[dst].AddRange(poleV2List[src]);
        }

        // [OPT-3] Insérer dans un bucket (lazy : jamais de Remove)
        public int BucketInsert(int linkIdx, float coutVal,
                                 float paramDijkstra, float pu, float maxBuckets)
        {
            int bucket = (int)Math.Truncate(Math.Min(
                Math.Pow(coutVal / paramDijkstra, pu), maxBuckets - 1));
            while (bucket >= gga_nq.Count)
                gga_nq.Add(new List<int>(64));
            gga_nq[bucket].Add(linkIdx);
            is_queue[linkIdx] = true;
            nb_pop++;
            return bucket;
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    //  ResultatOD — résultat d'une paire O-D (thread-safe via ConcurrentBag)
    // ══════════════════════════════════════════════════════════════════════
    public class ResultatOD
    {
        public int    numod, arrivee_link;
        public string p, q, libod, ligne_od, ligne_detour;
        public float  od;
        public List<string> lignes_temps, lignes_chemins, lignes_noeuds, lignes_isoles;
        // Accumulations à appliquer en séquentiel après la phase parallèle
        public List<(int linkIdx, float volau,
                     int svcIdx, float volauSvc,
                     float boai, float boatSvc,
                     float alij, float alitSvc)> accumulations;
    }

    // ══════════════════════════════════════════════════════════════════════
    //  Programme principal
    // ══════════════════════════════════════════════════════════════════════
    class Program
    {
        static void Main(string[] args)
        {
            // [OPT-8] args.Length au lieu de args.Count()
            if (args.Length > 3)
            {
                string nom_reseau     = args[0];
                string nom_matrice    = args[1];
                string nom_sortie     = args[2];
                string nom_parametres = args[3];
                string nom_penalites  = args.Length > 4 ? args[4] : null;
                affectation_tc(nom_reseau, nom_matrice, nom_sortie,
                               nom_parametres, nom_penalites);
            }
        }

        // ──────────────────────────────────────────────────────────────────
        //  Lecture des paramètres (inchangée sauf [OPT-4])
        // ──────────────────────────────────────────────────────────────────
        public static Param_affectation_horaire lit_parametres(string nomParametres)
        {
            var p = new Param_affectation_horaire();
            if (!File.Exists(nomParametres)) return p;

            using var r = new StreamReader(nomParametres);
            p.algorithme      = int.Parse(r.ReadLine().Split(';')[0]);
            p.demitours       = bool.Parse(r.ReadLine().Split(';')[0]);
            p.max_nb_buckets  = Formats.ParseFloat(r.ReadLine().Split(';')[0]);
            p.nb_jours        = int.Parse(r.ReadLine().Split(';')[0]);
            p.nom_matrice     = r.ReadLine().Split(';')[0];
            p.nom_penalites   = r.ReadLine().Split(';')[0];
            p.nom_reseau      = r.ReadLine().Split(';')[0];
            p.nom_sortie      = r.ReadLine().Split(';')[0];
            p.param_dijkstra  = Formats.ParseFloat(r.ReadLine().Split(';')[0]);
            p.pu              = Formats.ParseFloat(r.ReadLine().Split(';')[0]);
            p.sortie_chemins  = bool.Parse(r.ReadLine().Split(';')[0]);
            p.sortie_services = bool.Parse(r.ReadLine().Split(';')[0]);
            p.sortie_temps    = int.Parse(r.ReadLine().Split(';')[0]);
            if (p.sortie_temps >= 10) { p.sortie_stops = true;  p.sortie_temps -= 10; }
            else                      { p.sortie_stops = false; }
            p.sortie_turns    = bool.Parse(r.ReadLine().Split(';')[0]);
            p.texte_cboa      = r.ReadLine().Split(';')[0];
            p.texte_cmap      = r.ReadLine().Split(';')[0];
            p.texte_coef_tmap = r.ReadLine().Split(';')[0];
            p.texte_cveh      = r.ReadLine().Split(';')[0];
            p.texte_cwait     = r.ReadLine().Split(';')[0];
            p.texte_tboa      = r.ReadLine().Split(';')[0];
            p.texte_tboa_max  = r.ReadLine().Split(';')[0];

            if (!r.EndOfStream) p.tmapmax         = Formats.ParseFloat(r.ReadLine().Split(';')[0]);
            if (!r.EndOfStream) p.texte_toll       = r.ReadLine().Split(';')[0];
            if (!r.EndOfStream) p.texte_filtre_sortie = r.ReadLine().Split(';')[0];
            if (!r.EndOfStream) p.temps_max        = Formats.ParseFloat(r.ReadLine().Split(';')[0]);
            if (!r.EndOfStream) p.sortie_noeuds    = bool.Parse(r.ReadLine().Split(';')[0]);
            if (!r.EndOfStream) p.sortie_isoles    = bool.Parse(r.ReadLine().Split(';')[0]);

            p.test_OK = true;
            return p;
        }

        // ──────────────────────────────────────────────────────────────────
        public static void Ecrit_parametres(Param_affectation_horaire parametres,
                                             string nom_fichier_ini)
        {
            using var w = new StreamWriter(nom_fichier_ini, false, Encoding.UTF8);
            int sortie_temps_out = parametres.sortie_temps
                                 + (parametres.sortie_stops ? 10 : 0);
            w.WriteLine(parametres.algorithme      + ";algorithm");
            w.WriteLine(parametres.demitours       + ";prohibited U-turns");
            w.WriteLine(parametres.max_nb_buckets  + ";max buckets");
            w.WriteLine(parametres.nb_jours        + ";number of days");
            w.WriteLine(parametres.nom_matrice     + ";matrix file");
            w.WriteLine(parametres.nom_penalites   + ";turns and transfers file");
            w.WriteLine(parametres.nom_reseau      + ";network file");
            w.WriteLine(parametres.nom_sortie      + ";generic output file");
            w.WriteLine(parametres.param_dijkstra  + ";algorithm parameter+");
            w.WriteLine(parametres.pu              + ";algorithm power");
            w.WriteLine(parametres.sortie_chemins  + ";output paths");
            w.WriteLine(parametres.sortie_services + ";output services");
            w.WriteLine(sortie_temps_out           + ";output travel times");
            w.WriteLine(parametres.sortie_turns    + ";output turns and transfers");
            w.WriteLine(parametres.texte_cboa      + ";boarding weight");
            w.WriteLine(parametres.texte_cmap      + ";individual mode weight");
            w.WriteLine(parametres.texte_coef_tmap + ";individual travel time factor");
            w.WriteLine(parametres.texte_cveh      + ";in-vehicle time weight");
            w.WriteLine(parametres.texte_cwait     + ";wait time weight");
            w.WriteLine(parametres.texte_tboa      + ";min transfer time");
            w.WriteLine(parametres.texte_tboa_max  + ";max transfer time");
            w.WriteLine(parametres.tmapmax         + ";max individual travel time");
            w.WriteLine(parametres.texte_toll      + ";toll weight");
            w.WriteLine(parametres.texte_filtre_sortie + ";output filter types");
            w.WriteLine(parametres.temps_max       + ";max travel cost");
            w.WriteLine(parametres.sortie_noeuds   + ";output nodes");
            w.WriteLine(parametres.sortie_isoles   + ";output isolated links");
        }


        public static void affectation_tc(string nom_reseau, string nom_matrice,
            string nom_sortie, string nom_parametres, string nom_penalites)
        {
            var types    = new HashSet<string>();
            var turns    = new Dictionary<Turn, float>();
            var transfers= new Dictionary<Turn, float>();
            var link_id  = new Dictionary<Link_num, int>();
            var projet   = new etude();
            var aff_hor  = lit_parametres(nom_parametres);

            projet.param_affectation_horaire = aff_hor;
            aff_hor.nom_sortie   = nom_sortie;
            aff_hor.nom_reseau   = nom_reseau;
            aff_hor.nom_matrice  = nom_matrice;
            aff_hor.nom_penalites= nom_penalites;

            if (!File.Exists(nom_parametres) || !File.Exists(nom_reseau)
                || !File.Exists(nom_matrice) || !aff_hor.test_OK) return;

            // ── Import réseau ────────────────────────────────────────────
            if (projet.reseaux.Count > 0) projet.reseaux.RemoveAt(projet.reseaux.Count - 1);
            projet.reseaux.Add(new network());
            projet.reseau_actif = projet.reseaux.Count - 1;
            int num_res = projet.reseau_actif;

            // [OPT-1] Alias local — évite les accès imbriqués répétés
            var reseau = projet.reseaux[num_res];

            using var fich_log = new StreamWriter(aff_hor.nom_sortie + "_log.txt",
                                                  false, Encoding.UTF8);
            fich_log.AutoFlush = true;
            fich_log.WriteLine("Version: Muslic " +
                System.Reflection.Assembly.GetExecutingAssembly().GetName().Version);
            fich_log.WriteLine("Process start time: " +
                DateTime.Now.ToString("dddd dd MMMM yyyy HH:mm:ss.fff"));

            // Paramètres log (inchangé)
            fich_log.WriteLine("Minimum transfer time:"      + aff_hor.texte_tboa);
            fich_log.WriteLine("Maximum transfer time:"      + aff_hor.texte_tboa_max);
            fich_log.WriteLine("Transfer weight:"            + aff_hor.texte_cboa);
            fich_log.WriteLine("Wait weight:"                + aff_hor.texte_cwait);
            fich_log.WriteLine("Time based links weight:"    + aff_hor.texte_cveh);
            fich_log.WriteLine("Individual links weight:"    + aff_hor.texte_cmap);
            fich_log.WriteLine("Individual travel time factor:" + aff_hor.texte_coef_tmap);
            fich_log.WriteLine("Generalized travel time maximum:" + aff_hor.temps_max);
            fich_log.WriteLine("Individual travel time maximum:"  + aff_hor.tmapmax);
            fich_log.WriteLine("Toll weight:"                + aff_hor.texte_toll);
            fich_log.WriteLine("Number of days:"             + aff_hor.nb_jours);
            fich_log.WriteLine("Prohibited U-turns:"         + aff_hor.demitours);
            fich_log.WriteLine("Algorithm:"                  + aff_hor.algorithme);
            fich_log.WriteLine("Algorithm number of buckets:"+ aff_hor.max_nb_buckets);
            fich_log.WriteLine("Algorithm scale parameter:"  + aff_hor.param_dijkstra);
            fich_log.WriteLine("Algorithm power parameter:"  + aff_hor.pu);
            fich_log.WriteLine("Output paths:"               + aff_hor.sortie_chemins);
            fich_log.WriteLine("Output times:"               + aff_hor.sortie_temps);
            fich_log.WriteLine("Output filenames:"           + aff_hor.nom_sortie);
            fich_log.WriteLine("Link type filter:"           + aff_hor.texte_filtre_sortie);
            fich_log.WriteLine("Output nodes:"               + aff_hor.sortie_noeuds);
            fich_log.WriteLine("Output isolated nodes:"      + aff_hor.sortie_isoles);

            reseau.nom = Path.GetFileNameWithoutExtension(nom_reseau);

            // ── Import nœuds et liens ────────────────────────────────────
            ImporterReseau(reseau, nom_reseau, fich_log);

            // ── Construction de la topologie (pred/succ) ─────────────────
            // [OPT-1] var links/nodes locaux dans la boucle
            {
                var links = reseau.links;
                var nodes = reseau.nodes;
                for (int i = 0; i < links.Count; i++)
                {
                    nodes[links[i].nd].pred.Add(i);
                    nodes[links[i].no].succ.Add(i);
                }
            }

            fich_log.WriteLine("Network:" + nom_reseau);
            fich_log.WriteLine("Nodes:"   + reseau.nodes.Count);
            fich_log.WriteLine("Links:"   + reseau.links.Count);

            // ── Import pénalités ─────────────────────────────────────────
            if (File.Exists(nom_penalites))
                ImporterPenalites(reseau, nom_penalites, turns, transfers, fich_log);

            // ── Initialisation des paramètres de coûts ───────────────────
            InitialiserParametres(aff_hor, reseau);

            // [OPT-6] HashSet filtre précalculé UNE SEULE FOIS hors boucle
            var filtre = new HashSet<string>();
            if (aff_hor.texte_filtre_sortie.Trim().Length > 0)
                foreach (var f in aff_hor.texte_filtre_sortie.Split('|'))
                    if (f.Trim().Length > 0) filtre.Add(f.Trim());

            // ── Lecture matrice en mémoire ───────────────────────────────
            fich_log.WriteLine("Matrix:" + nom_matrice);
            var paires = LireMatrice(nom_matrice, aff_hor);
            fich_log.WriteLine($"OD pairs read: {paires.Count}");

            // ── Phase parallèle de calcul ─────────────────────────────────
            DateTime t1 = DateTime.Now;
            fich_log.WriteLine("Computation start time: " +
                t1.ToString("dddd dd MMMM yyyy HH:mm:ss.fff"));

            CalculerAffectationParallele(
                projet, paires, aff_hor, turns, filtre, nom_sortie, fich_log);

            fich_log.WriteLine("Computation end time: " +
                DateTime.Now.ToString("dddd dd MMMM yyyy HH:mm:ss.fff"));
            fich_log.WriteLine("Elapsed: " +
                (DateTime.Now - t1).ToString(@"hh\:mm\:ss\.fff"));

            // ── Écriture des sorties réseau (liens, services) ─────────────
            EcrireSortiesReseau(projet, aff_hor, transfers, fich_log);
        }

        // ══════════════════════════════════════════════════════════════════
        //  Import réseau (nœuds + liens) — [OPT-1] + [OPT-4]
        // ══════════════════════════════════════════════════════════════════
        static void ImporterReseau(network reseau, string nomReseau, StreamWriter log)
        {
            string carte = "t links";
            using var flux   = new FileStream(nomReseau, FileMode.Open,
                                              FileAccess.Read, FileShare.Read);
            using var reader = new StreamReader(flux, Encoding.UTF8, bufferSize: 131072);

            string chaine;
            while ((chaine = reader.ReadLine()) != null)
            {
                if (chaine.Trim().Length == 0) continue;

                if (chaine.Length >= 7 && chaine.Substring(0, 7) == "t nodes")
                    { carte = "t nodes"; continue; }
                if (chaine.Length >= 7 && chaine.Substring(0, 7) == "t links")
                    { carte = "t links"; continue; }

                // [OPT-1] Split une seule fois
                var ch = chaine.Split(Formats.Sep, StringSplitOptions.None);

                if (carte == "t nodes")
                    ImporterNoeud(reseau, ch);
                else
                    ImporterLien(reseau, ch);
            }
        }

        static void ImporterNoeud(network reseau, string[] ch)
        {
            string ni = ch[0].Trim();
            if (reseau.numnoeud.ContainsKey(ni)) return;

            // [OPT-4] ParseFloat unifié
            float xi = Formats.ParseFloat(ch[1]);
            float yi = Formats.ParseFloat(ch[2]);

            reseau.numnoeud.Add(ni, reseau.nodes.Count);
            var noeud = new node { i = ni, x = xi, y = yi, is_visible = true };
            if (ch.Length > 3) noeud.texte = ch[3];

            if (xi > reseau.xu) reseau.xu = xi;
            if (xi < reseau.xl) reseau.xl = xi;
            if (yi > reseau.yu) reseau.yu = yi;
            if (yi < reseau.yl) reseau.yl = yi;

            reseau.nodes.Add(noeud);
        }

        static void ImporterLien(network reseau, string[] ch)
        {
            if (ch.Length < 8) return;
            string ni = ch[0].Trim();
            string nj = ch[1].Trim();
            int line   = Convert.ToInt32(ch[4]);

            // Enregistrer les nœuds inconnus
            if (!reseau.numnoeud.ContainsKey(ni))
            {
                reseau.numnoeud.Add(ni, reseau.nodes.Count);
                reseau.nodes.Add(new node { i = ni });
            }
            if (!reseau.numnoeud.ContainsKey(nj))
            {
                reseau.numnoeud.Add(nj, reseau.nodes.Count);
                reseau.nodes.Add(new node { i = nj });
            }

            // Vérifier si ce lien (ni, nj, line) existe déjà
            var num_link = new Link_num { i = ni, j = nj, line = line };
            int existIdx;
            if (reseau.noms_arcs.ContainsKey(ni + ";" + nj + ";" + line))
            {
                // Ajouter un service au lien existant
                existIdx = int.Parse(reseau.noms_arcs[ni + ";" + nj + ";" + line]);
                var svc = ParseService(ch, reseau);
                if (svc.numero > 0)
                {
                    reseau.links[existIdx].services.Add(svc);
                    reseau.nbservices++;
                }
                return;
            }

            var lien = new link
            {
                no     = reseau.numnoeud[ni],
                nd     = reseau.numnoeud[nj],
                ligne  = line,
                temps  = Formats.ParseFloat(ch[2]),
                longueur = Formats.ParseFloat(ch[3]),
            };
            if (ch.Length > 9)  lien.texte = ch[9];
            if (ch.Length > 10) lien.type  = ch[10].Trim();
            if (ch.Length > 11) lien.toll  = Formats.ParseFloat(ch[11]);

            var service = ParseService(ch, reseau);
            if (service.numero > 0)
            {
                lien.services.Add(service);
                reseau.nbservices++;
            }

            reseau.noms_arcs[ni + ";" + nj + ";" + line] = reseau.links.Count.ToString();
            reseau.links.Add(lien);

            if (lien.type != null && int.TryParse(lien.type, out int typeInt)
                && typeInt > reseau.max_type)
                reseau.max_type = typeInt;
        }

        static Service ParseService(string[] ch, network reseau = null)
        {
            var s = new Service { numero = -1 };
            if (ch.Length > 7)
            {
                s.numero = Formats.ParseInt(ch[5]);
                s.hd     = Formats.ParseFloat(ch[6]);
                s.hf     = Formats.ParseFloat(ch[7]);
            }
            if (ch.Length > 8)
            {
                string regStr = ch[8].Trim();
                if (int.TryParse(regStr, out int regVal))
                {
                    s.regime = regVal;
                }
                else if (reseau != null)
                {
                    // ch[8] est un nom de calendrier (ex: 'NNNNONN') → lookup dans num_calendrier
                    if (!reseau.num_calendrier.TryGetValue(regStr, out s.regime))
                    {
                        // Calendrier inconnu : l'enregistrer
                        s.regime = reseau.nom_calendrier.Count;
                        reseau.num_calendrier[regStr] = s.regime;
                        reseau.nom_calendrier.Add(regStr);
                    }
                }
            }
            return s;
        }

        // ══════════════════════════════════════════════════════════════════
        //  Import pénalités — [OPT-1] + [OPT-4]
        // ══════════════════════════════════════════════════════════════════
        static void ImporterPenalites(network reseau, string nomPenalites,
            Dictionary<Turn,float> turns, Dictionary<Turn,float> transfers,
            StreamWriter log)
        {
            log.WriteLine("Penalties and transfers:" + nomPenalites);
            using var flux   = new FileStream(nomPenalites, FileMode.Open,
                                              FileAccess.Read, FileShare.Read);
            using var reader = new StreamReader(flux, Encoding.UTF8, bufferSize: 65536);

            // [OPT-1] Alias
            var links = reseau.links;
            var nodes = reseau.nodes;

            string chaine;
            while ((chaine = reader.ReadLine()) != null)
            {
                if (chaine.Trim().Length == 0) continue;
                var penal = chaine.Split(Formats.Sep,
                                         StringSplitOptions.RemoveEmptyEntries);
                if (penal.Length < 6) continue;

                int nj     = reseau.numnoeud[penal[0].Trim()];
                int ni     = reseau.numnoeud[penal[1].Trim()];
                int linei  = int.Parse(penal[2]);
                int nk     = reseau.numnoeud[penal[3].Trim()];
                int linej  = int.Parse(penal[4]);
                float tps  = Formats.ParseFloat(penal[5]);

                // Trouver l'arc entrant (ni→nj, ligne linei)
                int ntri = -1, ntrj = -1;
                foreach (int k in nodes[nj].pred)
                {
                    var lk = links[k];
                    if (lk.no == ni && lk.ligne == linei) { ntri = k; break; }
                }
                // Trouver l'arc sortant (nj→nk, ligne linej)
                foreach (int k in nodes[nj].succ)
                {
                    var lk = links[k];
                    if (lk.nd == nk && lk.ligne == linej) { ntrj = k; break; }
                }
                if (ntri < 0 || ntrj < 0) continue;

                nodes[nj].is_intersection = true;
                var virage = new Turn { arci = ntri, arcj = ntrj };
                if (tps >= 0)
                    turns[virage]     = tps;
                else
                    transfers[virage] = Math.Abs(tps);
            }
        }

        // ══════════════════════════════════════════════════════════════════
        //  Initialisation des dictionnaires de paramètres par type de lien
        // ══════════════════════════════════════════════════════════════════
        static void InitialiserParametres(Param_affectation_horaire p, network reseau)
        {
            var types = new HashSet<string>();
            foreach (var lien in reseau.links)
                if (lien.type != null) types.Add(lien.type);

            void InitDict(Dictionary<string,float> d, string texte, float defVal)
            {
                d.Clear();
                var parts = texte?.Split('|') ?? Array.Empty<string>();
                foreach (var t in types)
                {
                    if (int.TryParse(t, out int ti) && ti < parts.Length)
                        d[t] = Formats.ParseFloat(parts[ti]);
                    else
                        d[t] = parts.Length > 0 ? Formats.ParseFloat(parts[0]) : defVal;
                }
                if (!d.ContainsKey("0")) d["0"] = defVal;
            }

            InitDict(p.cveh,      p.texte_cveh,      1f);
            InitDict(p.cwait,     p.texte_cwait,      1f);
            InitDict(p.cmap,      p.texte_cmap,       1f);
            InitDict(p.cboa,      p.texte_cboa,       1f);
            InitDict(p.coef_tmap, p.texte_coef_tmap,  1f);
            InitDict(p.tboa,      p.texte_tboa,       0f);
            InitDict(p.tboa_max,  p.texte_tboa_max,   1440f);
            InitDict(p.ctoll,     p.texte_toll,       0f);
        }

        // ══════════════════════════════════════════════════════════════════
        //  Lecture matrice O-D en mémoire — [OPT-4]
        // ══════════════════════════════════════════════════════════════════
        static List<PaireOD> LireMatrice(string nomMatrice,
                                          Param_affectation_horaire aff_hor)
        {
            var paires = new List<PaireOD>(50000);
            int numod  = 0;

            using var reader = new StreamReader(
                new FileStream(nomMatrice, FileMode.Open,
                               FileAccess.Read, FileShare.Read),
                Encoding.UTF8, bufferSize: 131072);

            string chaine;
            while ((chaine = reader.ReadLine()) != null)
            {
                if (chaine.Trim().Length == 0) continue;
                var ch = chaine.Split(Formats.Sep,
                                      StringSplitOptions.RemoveEmptyEntries);
                if (ch.Length < 5) continue;

                numod++;
                var od = new PaireOD
                {
                    numod   = numod,
                    p       = ch[0].Trim(),
                    q       = ch[1].Trim(),
                    od      = Formats.ParseFloat(ch[2]),
                    jour    = (int)Formats.ParseFloat(ch[3]),
                    horaire = Formats.ParseFloat(ch[4]),
                    sens    = 1,
                    libod   = numod.ToString(),
                };

                if (ch.Length > 5)
                    od.sens = ch[5].ToLower() == "a" ? 2 : 1;
                if (ch.Length > 6 && ch[6].Trim().Length > 0)
                    od.libod = ch[6].Trim();

                // Paramètres spécifiques à la paire (colonnes 7+)
                od.a_params_specifiques = ch.Length > 17;
                if (od.a_params_specifiques)
                {
                    od.cveh      = ParseDictParams(ch[7]);
                    od.cwait     = ParseDictParams(ch[8]);
                    od.cmap      = ParseDictParams(ch[9]);
                    od.cboa      = ParseDictParams(ch[10]);
                    od.coef_tmap = ParseDictParams(ch[11]);
                    od.tboa      = ParseDictParams(ch[12]);
                    od.tboa_max  = ParseDictParams(ch[13]);
                    od.ctoll     = ch.Length > 16 ? ParseDictParams(ch[16])
                                                  : new Dictionary<string,float>{{"0",0f}};
                }
                if (ch.Length > 23)
                {
                    od.sortie_chemins  = bool.Parse(ch[18]);
                    od.sortie_temps    = int.Parse(ch[19]);
                    od.algorithme      = int.Parse(ch[20]);
                    od.param_dijkstra  = Formats.ParseFloat(ch[21]);
                    od.max_nb_buckets  = Formats.ParseFloat(ch[22]);
                    od.pu              = Formats.ParseFloat(ch[23]);
                }
                else
                {
                    od.sortie_chemins = aff_hor.sortie_chemins;
                    od.sortie_temps   = aff_hor.sortie_temps;
                    od.algorithme     = aff_hor.algorithme;
                    od.param_dijkstra = aff_hor.param_dijkstra;
                    od.max_nb_buckets = aff_hor.max_nb_buckets;
                    od.pu             = aff_hor.pu;
                }
                od.texte_filtre_sortie = ch.Length > 24 ? ch[24]
                                        : aff_hor.texte_filtre_sortie;
                paires.Add(od);
            }
            return paires;
        }

        static Dictionary<string,float> ParseDictParams(string texte)
        {
            var d    = new Dictionary<string,float>();
            var vals = texte.Replace(",",".").Split('|');
            for (int k = 0; k < vals.Length; k++)
                d[k.ToString()] = Formats.ParseFloat(vals[k]);
            if (!d.ContainsKey("0") && vals.Length > 0)
                d["0"] = Formats.ParseFloat(vals[0]);
            return d;
        }

        // ══════════════════════════════════════════════════════════════════
        //  [PAR-2] Phase parallèle — Parallel.ForEach par groupe d'origines
        // ══════════════════════════════════════════════════════════════════
        static void CalculerAffectationParallele(
            etude projet, List<PaireOD> paires,
            Param_affectation_horaire aff_hor,
            Dictionary<Turn,float> turns,
            HashSet<string> filtre,
            string nomSortie, StreamWriter fich_log)
        {
            var reseau    = projet.reseaux[projet.reseau_actif];
            int nbLinks   = reseau.links.Count;
            int nbBuckets = (int)aff_hor.max_nb_buckets;

            // [PAR-2] Grouper par (origine, jour, horaire, sens)
            var groupes = paires
                .GroupBy(od => (od.p, od.jour, od.horaire, od.sens))
                .ToList();

            fich_log.WriteLine($"Origin groups: {groupes.Count}");

            // Écriture des en-têtes de fichiers
            Ecrit_parametres(aff_hor, nomSortie + "_param.txt");

            var fOD      = new StreamWriter(nomSortie + "_od.txt",      false, Encoding.UTF8, 65536);
            var fChemins = new StreamWriter(nomSortie + "_chemins.txt",  false, Encoding.UTF8, 65536);
            var fTemps   = new StreamWriter(nomSortie + "_temps.txt",    false, Encoding.UTF8, 65536);
            var fNoeuds  = new StreamWriter(nomSortie + "_noeuds.txt",   false, Encoding.UTF8, 65536);
            var fDetour  = new StreamWriter(nomSortie + "_detour.txt",   false, Encoding.UTF8, 65536);
            var fIsoles  = new StreamWriter(nomSortie + "_isoles.txt",   false, Encoding.UTF8, 65536);

            fOD.WriteLine("id;o;d;jour;heureo;heured;temps;tveh;tmap;tatt;tcorr;ncorr;tatt1;cout;longueur;pole;volau;texte;nbpop;toll");
            fChemins.WriteLine("id;o;d;jour;heure;i;j;ij;ligne;service;temps;heureo;tveh;tmap;tatt;tcorr;ncorr;tatt1;cout;longueur;pole;volau;boai;alij;texte;type;toll");
            if (aff_hor.sortie_temps == 3)
            {
                fTemps.WriteLine("o;ij;ligne;temps;tatt1;volau");
                fNoeuds.WriteLine("o;numero;temps;tatt1;volau");
            }
            else
            {
                fTemps.WriteLine("id;o;ij;ligne;numtrc;jour;heureo;heured;temps;tveh;tmap;tatt;tcorr;ncorr;tatt1;cout;longueur;pole;volau;precedent;type;toll;ti");
                fNoeuds.WriteLine("id;o;d;jour;numero;heureo;heured;temps;tveh;tmap;tatt;tcorr;ncorr;tatt1;cout;longueur;pole;toll;volau;stops");
            }

            // [PAR-3] Channels pour l'écriture asynchrone
            var chOD      = Channel.CreateUnbounded<string>(new UnboundedChannelOptions{SingleReader=true});
            var chChemins = Channel.CreateUnbounded<string>(new UnboundedChannelOptions{SingleReader=true});
            var chTemps   = Channel.CreateUnbounded<string>(new UnboundedChannelOptions{SingleReader=true});
            var chNoeuds  = Channel.CreateUnbounded<string>(new UnboundedChannelOptions{SingleReader=true});
            var chDetour  = Channel.CreateUnbounded<string>(new UnboundedChannelOptions{SingleReader=true});
            var chIsoles  = Channel.CreateUnbounded<string>(new UnboundedChannelOptions{SingleReader=true});

            var wOD      = EcrireDepuisChannel(chOD.Reader,      fOD);
            var wChemins = EcrireDepuisChannel(chChemins.Reader,  fChemins);
            var wTemps   = EcrireDepuisChannel(chTemps.Reader,    fTemps);
            var wNoeuds  = EcrireDepuisChannel(chNoeuds.Reader,   fNoeuds);
            var wDetour  = EcrireDepuisChannel(chDetour.Reader,   fDetour);
            var wIsoles  = EcrireDepuisChannel(chIsoles.Reader,   fIsoles);

            // [PAR-1] Un DijkstraState par thread
            var threadState = new ThreadLocal<DijkstraState>(
                () => new DijkstraState(nbLinks, nbBuckets));

            var resultats = new ConcurrentBag<ResultatOD>();

            int nbCores = Math.Max(1, Environment.ProcessorCount - 1);
            Console.WriteLine();
            Console.WriteLine($"Parallelism: {nbCores} threads");
            int ctop  = Console.CursorTop;
            int cleft = Console.CursorLeft;

            // Compteur d'avancement thread-safe
            int groupesDone = 0;
            int totalGroupes = groupes.Count;

            Parallel.ForEach(
                groupes,
                new ParallelOptions { MaxDegreeOfParallelism = nbCores },
                groupe =>
                {
                    var state  = threadState.Value;
                    state.Reset();

                    var p0 = groupe.First();

                    var eff = p0.a_params_specifiques
                        ? FusionnerParametres(aff_hor, p0)
                        : aff_hor;

                    bool ok = p0.sens == 1
                        ? DijkstraSens1(reseau, eff, state, p0, turns)
                        : DijkstraSens2(reseau, eff, state, p0, turns);

                    foreach (var paire in groupe)
                    {
                        var res = ExtraireResultat(reseau, eff, state, paire, filtre, ok);
                        resultats.Add(res);

                        if (res.ligne_od != null)
                            chOD.Writer.TryWrite(res.ligne_od);
                        if (res.lignes_chemins != null)
                            foreach (var l in res.lignes_chemins)
                                chChemins.Writer.TryWrite(l);
                        if (res.lignes_temps != null)
                            foreach (var l in res.lignes_temps)
                                chTemps.Writer.TryWrite(l);
                        if (res.lignes_noeuds != null)
                            foreach (var l in res.lignes_noeuds)
                                chNoeuds.Writer.TryWrite(l);
                        if (res.ligne_detour != null)
                            chDetour.Writer.TryWrite(res.ligne_detour);
                        if (res.lignes_isoles != null)
                            foreach (var l in res.lignes_isoles)
                                chIsoles.Writer.TryWrite(l);
                    }

                    // Affichage avancement
                    int done = Interlocked.Increment(ref groupesDone);
                    int pct  = (int)(100L * done / totalGroupes);
                    Console.SetCursorPosition(cleft, ctop);
                    Console.Write($"Shortest paths computing...:{pct}%  ");
                });

            Console.SetCursorPosition(cleft, ctop);
            Console.Write("Shortest paths computing...:100%");

            // Fermer les channels
            chOD.Writer.Complete();     chChemins.Writer.Complete();
            chTemps.Writer.Complete();  chNoeuds.Writer.Complete();
            chDetour.Writer.Complete(); chIsoles.Writer.Complete();
            Task.WaitAll(wOD, wChemins, wTemps, wNoeuds, wDetour, wIsoles);
            fOD.Close(); fChemins.Close(); fTemps.Close();
            fNoeuds.Close(); fDetour.Close(); fIsoles.Close();
            threadState.Dispose();

            // [PAR-4] Accumulations séquentielles (volau, boai, alij)
            AppliquerAccumulations(reseau, resultats);

            fich_log.WriteLine($"Computation end: {DateTime.Now:dddd dd MMMM yyyy HH:mm:ss.fff}");
        }

        // ══════════════════════════════════════════════════════════════════
        //  Dijkstra sens 1 (heure de départ)
        //  [OPT-1] Variables locales pour cacher les accès
        //  [OPT-2] EnsureInit lazy
        //  [OPT-3] BucketInsert sans Remove
        //  [OPT-5] poleV2 comme List<string>
        // ══════════════════════════════════════════════════════════════════
        static bool DijkstraSens1(
            network reseau, Param_affectation_horaire p,
            DijkstraState st, PaireOD paire,
            Dictionary<Turn,float> turns)
        {
            // [OPT-1] Alias locaux
            var links  = reseau.links;
            var nodes  = reseau.nodes;
            string depart  = paire.p;
            float  horaire = paire.horaire;
            int    jour    = paire.jour;

            if (!reseau.numnoeud.TryGetValue(depart, out int nodeDepart))
                return false;

            // ── Initialisation depuis les successeurs de l'origine ────────
            var succOrigine = nodes[nodeDepart].succ;
            for (int j = 0; j < succOrigine.Count; j++)
            {
                int  succ     = succOrigine[j];
                var  lsucc    = links[succ];
                st.EnsureInit(succ, lsucc.services.Count);
                string stype  = lsucc.type ?? "0";

                float cveh_s   = GetParam(p.cveh,      stype);
                float cmap_s   = GetParam(p.cmap,      stype);
                float ctoll_s  = GetParam(p.ctoll,     stype);
                float ctmap_s  = GetParam(p.coef_tmap, stype);

                if (lsucc.ligne < 0 && cmap_s > 0 && lsucc.temps < p.tmapmax)
                {
                    // Lien mode individuel depuis l'origine
                    bool test_periode = false;
                    if (lsucc.services.Count > 0)
                    {
                        int decal = (int)Math.Floor(horaire / 1440f);
                        for (int kk = 0; kk < lsucc.services.Count; kk++)
                        {
                            var svc = lsucc.services[kk];
                            if (decal <= p.nb_jours
                                && reseau.nom_calendrier[svc.regime].Substring(jour + decal, 1) == "O"
                                && svc.hd + 1440f * decal <= horaire
                                && svc.hf + 1440f * decal >  horaire)
                            {
                                test_periode = true;
                                st.service[succ] = kk;
                            }
                        }
                    }
                    else test_periode = true;

                    if (test_periode)
                    {
                        st.cout[succ]       = lsucc.temps * ctmap_s * cmap_s
                                            + lsucc.toll  * ctoll_s;
                        st.touche[succ]     = 1;
                        st.h[succ]          = horaire + lsucc.temps * ctmap_s;
                        st.l[succ]          = lsucc.longueur;
                        st.tmap[succ]       = lsucc.temps * ctmap_s;
                        st.ttoll[succ]      = lsucc.toll;
                        st.pivot[succ]      = -1;
                        st.turn_pivot[succ] = -1;
                        st.pole[succ]       = depart;
                        st.poleV2List[succ].Clear();
                        st.BucketInsert(succ, st.cout[succ],
                                        p.param_dijkstra, p.pu, p.max_nb_buckets);
                    }
                }
                else if (cveh_s > 0)
                {
                    // Lien TC : chercher le meilleur service
                    int num_svc = -1;
                    float cout2 = 1e38f;
                    for (int ii = 0; ii < lsucc.services.Count; ii++)
                    {
                        var svc    = lsucc.services[ii];
                        float hdD  = svc.hd + st.delta_service[succ][ii] * 1440f;
                        if (hdD < horaire
                            || reseau.nom_calendrier[svc.regime].Substring(jour, 1) == "N")
                        {
                            // Chercher le prochain jour opérationnel
                            int duree = reseau.nom_calendrier[svc.regime].Length;
                            for (int jj = jour+1;
                                 jj <= Math.Min(jour + p.nb_jours, duree-1); jj++)
                            {
                                if (reseau.nom_calendrier[svc.regime].Substring(jj,1)=="O"
                                    && svc.hd + (-jour+jj)*1440f >= horaire)
                                {
                                    float h2 = (-jour + jj);
                                    if (st.delta_service[succ][ii] < h2
                                        || st.touche[succ] == 0)
                                        st.delta_service[succ][ii] = h2;
                                    hdD = svc.hd + st.delta_service[succ][ii]*1440f;
                                    break;
                                }
                            }
                        }
                        float hfD  = svc.hf + st.delta_service[succ][ii] * 1440f;
                        float wait = hdD - horaire;
                        if (wait < 0) continue;
                        float c = (svc.hf - svc.hd) * cveh_s + wait * GetParam(p.cwait, stype)
                                + lsucc.toll * ctoll_s;
                        if (c < cout2) { cout2 = c; num_svc = ii; }
                    }
                    if (num_svc >= 0)
                    {
                        var svc = lsucc.services[num_svc];
                        st.service[succ]    = num_svc;
                        st.cout[succ]       = cout2;
                        st.touche[succ]     = 1;
                        st.h[succ]          = svc.hf + st.delta_service[succ][num_svc]*1440f;
                        st.tatt[succ]       = svc.hd + st.delta_service[succ][num_svc]*1440f - horaire;
                        st.tatt1[succ]      = st.tatt[succ];
                        st.tveh[succ]       = svc.hf - svc.hd;
                        st.tcor[succ]       = 0f;
                        st.ncorr[succ]      = 1f;
                        st.l[succ]          = lsucc.longueur;
                        st.tmap[succ]       = 0f;
                        st.ttoll[succ]      = lsucc.toll;
                        st.pivot[succ]      = -1;
                        st.turn_pivot[succ] = -1;
                        st.pole[succ]       = nodes[lsucc.no].i;
                        st.poleV2List[succ].Clear();
                        st.poleV2List[succ].Add(nodes[lsucc.no].i);
                        st.BucketInsert(succ, st.cout[succ],
                                        p.param_dijkstra, p.pu, p.max_nb_buckets);
                    }
                }
            }

            // ── Boucle principale GGA ─────────────────────────────────────
            int bucket_max = (int)Math.Truncate(Math.Min(
                Math.Pow(p.temps_max / p.param_dijkstra, p.pu),
                p.max_nb_buckets - 1));

            while (st.id_bucket < st.gga_nq.Count && st.id_bucket <= bucket_max)
            {
                // Avancer au premier bucket non vide
                while (st.id_bucket < st.gga_nq.Count
                       && st.gga_nq[st.id_bucket].Count == 0)
                    st.id_bucket++;
                if (st.id_bucket >= st.gga_nq.Count
                    || st.id_bucket > bucket_max) break;

                // [OPT-3] Sélection pivot avec lazy deletion
                int pivot = -1, id_pivot = -1;
                var bucket = st.gga_nq[st.id_bucket];

                if (p.algorithme == 0)
                {
                    // FIFO : premier élément valide
                    while (bucket.Count > 0)
                    {
                        int cand = bucket[0];
                        bucket.RemoveAt(0);
                        // [OPT-3] Ignorer les éléments obsolètes
                        if (st.touche[cand] != 3) { pivot = cand; break; }
                    }
                }
                else
                {
                    // Min-cost in bucket avec lazy deletion
                    double cout_min = 1e38;
                    for (int k = bucket.Count - 1; k >= 0; k--)
                    {
                        int cand = bucket[k];
                        if (st.touche[cand] == 3)   // déjà finalisé : purger
                        { bucket.RemoveAt(k); continue; }
                        if (st.cout[cand] < cout_min)
                        { cout_min = st.cout[cand]; id_pivot = k; }
                    }
                    if (id_pivot >= 0)
                    {
                        pivot = bucket[id_pivot];
                        bucket.RemoveAt(id_pivot);
                    }
                }
                if (pivot < 0) { st.id_bucket++; continue; }
                st.touche[pivot] = 3; // finalisé

                // [OPT-1] Alias pivot
                var lp       = links[pivot];
                int nd_pivot = lp.nd;

                var succPivot = nodes[nd_pivot].succ;
                for (int j = 0; j < succPivot.Count; j++)
                {
                    int  succ  = succPivot[j];
                    var  ls    = links[succ];
                    st.EnsureInit(succ, ls.services.Count);
                    string stype = ls.type ?? "0";

                    // Demi-tours interdits
                    float penalite = 0f;
                    if (p.demitours && lp.no == ls.nd) { penalite = -1f; }
                    else if (nodes[nd_pivot].is_intersection)
                    {
                        var vir = new Turn { arci = pivot, arcj = succ };
                        if (turns.TryGetValue(vir, out float vp)) penalite = vp;
                    }
                    if (penalite < 0f) continue;

                    float tcorr = penalite > 0 ? penalite : GetParam(p.tboa, stype);
                    float tcorrmax = GetParam(p.tboa_max, stype);
                    float cveh_s  = GetParam(p.cveh,      stype);
                    float cmap_s  = GetParam(p.cmap,      stype);
                    float ctoll_s = GetParam(p.ctoll,     stype);
                    float ctmap_s = GetParam(p.coef_tmap, stype);
                    float cwait_s = GetParam(p.cwait,     stype);
                    float cboa_s  = GetParam(p.cboa,      stype);

                    // ── Cas 1 : lien mode individuel ─────────────────────
                    if (ls.ligne < 0 && cmap_s > 0
                        && st.tmap[pivot] + ls.temps < p.tmapmax)
                    {
                        float new_cout = st.cout[pivot]
                            + (ls.temps + penalite) * ctmap_s * cmap_s
                            + ls.toll * ctoll_s;

                        if (new_cout < st.cout[succ] || st.touche[succ] == 0)
                        {
                            st.cout[succ]       = new_cout;
                            st.touche[succ]     = 2;
                            st.h[succ]          = st.h[pivot] + ls.temps * ctmap_s + penalite;
                            st.l[succ]          = st.l[pivot] + ls.longueur;
                            st.tmap[succ]       = st.tmap[pivot] + (ls.temps + penalite) * ctmap_s;
                            st.ttoll[succ]      = st.ttoll[pivot] + ls.toll;
                            st.tatt[succ]       = st.tatt[pivot];
                            st.tatt1[succ]      = st.tatt1[pivot];
                            st.tveh[succ]       = st.tveh[pivot];
                            st.tcor[succ]       = st.tcor[pivot];
                            st.ncorr[succ]      = st.ncorr[pivot];
                            st.pivot[succ]      = pivot;
                            st.turn_pivot[succ] = j;
                            st.pole[succ]       = st.pole[pivot];
                            st.CopyPoleV2(succ, pivot); // [OPT-5]
                            if (lp.ligne > 0)
                                st.poleV2List[succ].Add(nodes[ls.no].i);
                            st.BucketInsert(succ, new_cout,
                                            p.param_dijkstra, p.pu, p.max_nb_buckets);
                        }
                    }
                    // ── Cas 2 : même ligne TC ─────────────────────────────
                    else if (ls.ligne == lp.ligne && cveh_s > 0 && lp.ligne > 0)
                    {
                        int num_svc = -1;
                        int pivot_svc = st.service[pivot];
                        if (pivot_svc < 0) continue;
                        int pivot_num = lp.services[pivot_svc].numero;

                        for (int ii = 0; ii < ls.services.Count; ii++)
                        {
                            var svc = ls.services[ii];
                            if (svc.numero == pivot_num
                                && svc.hd >= lp.services[pivot_svc].hf)
                            { num_svc = ii; break; }
                        }
                        if (num_svc < 0) continue;

                        var svc2    = ls.services[num_svc];
                        float delta = st.delta_service[pivot][pivot_svc];
                        st.delta_service[succ][num_svc] = delta;
                        float hf_d  = svc2.hf + delta * 1440f;
                        float new_cout = st.cout[pivot]
                            + (hf_d - st.h[pivot]) * cveh_s
                            + ls.toll * ctoll_s;

                        if (new_cout < st.cout[succ] || st.touche[succ] == 0)
                        {
                            st.service[succ]    = num_svc;
                            st.cout[succ]       = new_cout;
                            st.touche[succ]     = 1;
                            st.h[succ]          = hf_d;
                            st.tatt[succ]       = st.tatt[pivot];
                            st.tatt1[succ]      = st.tatt1[pivot];
                            st.tveh[succ]       = st.tveh[pivot]
                                                + hf_d - st.h[pivot];
                            st.tcor[succ]       = st.tcor[pivot];
                            st.ncorr[succ]      = st.ncorr[pivot];
                            st.l[succ]          = st.l[pivot] + ls.longueur;
                            st.tmap[succ]       = st.tmap[pivot];
                            st.ttoll[succ]      = st.ttoll[pivot] + ls.toll;
                            st.pivot[succ]      = pivot;
                            st.turn_pivot[succ] = j;
                            st.pole[succ]       = st.pole[pivot];
                            st.CopyPoleV2(succ, pivot);
                            st.BucketInsert(succ, new_cout,
                                            p.param_dijkstra, p.pu, p.max_nb_buckets);
                        }
                    }
                    // ── Cas 3 : correspondance TC lignes différentes ───────
                    else if (ls.ligne != lp.ligne && cveh_s > 0 && ls.ligne > 0)
                    {
                        int   num_svc = -1;
                        float cout2   = 1e38f;

                        for (int ii = 0; ii < ls.services.Count; ii++)
                        {
                            var svc = ls.services[ii];
                            int delta = 0;
                            int duree = reseau.nom_calendrier[svc.regime].Length;
                            float hdD = svc.hd + st.delta_service[succ][ii] * 1440f;

                            if (hdD < st.h[pivot] + tcorr
                                || reseau.nom_calendrier[svc.regime]
                                         .Substring(jour, 1) == "N")
                            {
                                float h2 = 1e38f; int h3 = -1;
                                for (int jj = jour+1;
                                     jj <= Math.Min(jour+p.nb_jours, duree-1); jj++)
                                {
                                    float hd_jj = svc.hd + (-jour+jj)*1440f;
                                    if (reseau.nom_calendrier[svc.regime]
                                              .Substring(jj,1) == "O"
                                        && hd_jj < h2
                                        && hd_jj - tcorr > st.h[pivot])
                                    { h2 = (-jour+jj); h3 = jj; }
                                }
                                if (h3 != -1)
                                {
                                    if (st.delta_service[succ][ii] < h2
                                        || st.touche[succ] == 0)
                                        st.delta_service[succ][ii] = h2;
                                    hdD = svc.hd + st.delta_service[succ][ii]*1440f;
                                }
                                else { delta = -1; }
                            }
                            if (delta < 0) continue;

                            float hfD   = svc.hf + st.delta_service[succ][ii]*1440f;
                            float wait  = hdD - st.h[pivot];
                            if (hdD >= st.h[pivot] + tcorr
                                && hdD <  st.h[pivot] + tcorrmax)
                            {
                                float c = st.cout[pivot]
                                    + (svc.hf - svc.hd) * cveh_s
                                    + wait * cwait_s
                                    + tcorr * cboa_s
                                    + ls.toll * ctoll_s;
                                if (c < cout2) { cout2 = c; num_svc = ii; }
                            }
                        }

                        if (num_svc >= 0
                            && (cout2 < st.cout[succ] || st.touche[succ] == 0))
                        {
                            var svc  = ls.services[num_svc];
                            float hfD = svc.hf + st.delta_service[succ][num_svc]*1440f;
                            float hdD = svc.hd + st.delta_service[succ][num_svc]*1440f;

                            st.service[succ]    = num_svc;
                            st.cout[succ]       = cout2;
                            st.touche[succ]     = 2;
                            st.h[succ]          = hfD;
                            st.tatt1[succ]      = st.ncorr[pivot] == 0
                                                  ? hdD - st.h[pivot]
                                                  : st.tatt1[pivot];
                            st.tatt[succ]       = st.tatt[pivot] + hdD - st.h[pivot];
                            st.tveh[succ]       = st.tveh[pivot] + svc.hf - svc.hd;
                            st.tcor[succ]       = st.tcor[pivot] + tcorr;
                            st.ncorr[succ]      = st.ncorr[pivot] + 1;
                            st.l[succ]          = st.l[pivot] + ls.longueur;
                            st.tmap[succ]       = st.tmap[pivot];
                            st.ttoll[succ]      = st.ttoll[pivot] + ls.toll;
                            st.pivot[succ]      = pivot;
                            st.turn_pivot[succ] = j;
                            st.pole[succ]       = st.pole[pivot] == depart
                                                  ? nodes[ls.no].i
                                                  : st.pole[pivot];
                            st.CopyPoleV2(succ, pivot); // [OPT-5]
                            if (lp.ligne > 0)
                            {
                                st.poleV2List[succ].Add(nodes[ls.no].i);
                                st.poleV2List[succ].Add(nodes[ls.no].i);
                            }
                            else
                                st.poleV2List[succ].Add(nodes[ls.no].i);

                            st.BucketInsert(succ, cout2,
                                            p.param_dijkstra, p.pu, p.max_nb_buckets);
                        }
                    }
                }
            }
            return true;
        }

        // DijkstraSens2 (heure d'arrivée) — parcourt les pred depuis q
        // DijkstraSens2 : heure d'arrivée en q.
        // Transcription fidèle de l'original (sens==2).
        // Init : pred de q. Boucle GGA : pred du nœud .no du pivot (identique sens 1).
        // Extraction du résultat : meilleur succ de p (voir ExtraireResultat).
        static bool DijkstraSens2(
            network reseau, Param_affectation_horaire p,
            DijkstraState st, PaireOD paire,
            Dictionary<Turn,float> turns)
        {
            var links   = reseau.links;
            var nodes   = reseau.nodes;
            string depart = paire.q;
            float  horaire = paire.horaire;
            int    jour    = paire.jour;

            if (!reseau.numnoeud.TryGetValue(depart, out int nodeDepart))
                return false;

            // ── Initialisation : prédécesseurs de q ─────────────────────
            var predQ = nodes[nodeDepart].pred;
            for (int j = 0; j < predQ.Count; j++)
            {
                int  predecesseur = predQ[j];
                var  lpred        = links[predecesseur];
                st.EnsureInit(predecesseur, lpred.services.Count);
                string pred_type  = lpred.type ?? "0";
                float  max_corr   = GetParam(p.tboa_max, pred_type);

                if (lpred.ligne < 0
                    && GetParam(p.cmap, pred_type) > 0
                    && lpred.temps < p.tmapmax)
                {
                    // Lien mode individuel
                    bool test_periode = false;
                    if (lpred.services.Count > 0)
                    {
                        int decal = (int)Math.Floor(horaire / 1440f);
                        for (int kk = 0; kk < lpred.services.Count; kk++)
                        {
                            var svc = lpred.services[kk];
                            if (Math.Abs(decal) <= p.nb_jours
                                && reseau.nom_calendrier[svc.regime].Substring(jour + decal, 1) == "O"
                                && svc.hd + 1440f * decal <= horaire
                                && svc.hf + 1440f * decal >  horaire)
                            { test_periode = true; st.service[predecesseur] = kk; }
                        }
                    }
                    else test_periode = true;

                    if (test_periode)
                    {
                        float ctmap = GetParam(p.coef_tmap, pred_type);
                        float cmap  = GetParam(p.cmap,      pred_type);
                        float ctoll = GetParam(p.ctoll,     pred_type);
                        st.touche[predecesseur]     = 1;
                        st.cout[predecesseur]       = lpred.temps * ctmap * cmap + lpred.toll * ctoll;
                        st.tmap[predecesseur]       = lpred.temps * ctmap;
                        st.ttoll[predecesseur]      = lpred.toll;
                        st.h[predecesseur]          = horaire - lpred.temps * ctmap;
                        st.l[predecesseur]          = lpred.longueur;
                        st.pivot[predecesseur]      = -1;
                        st.turn_pivot[predecesseur] = -1;
                        st.pole[predecesseur]       = depart;
                        st.poleV2List[predecesseur].Clear();
                        st.BucketInsert(predecesseur, st.cout[predecesseur],
                                        p.param_dijkstra, p.pu, p.max_nb_buckets);
                    }
                }
                else if (GetParam(p.cveh, pred_type) > 0)
                {
                    // Lien TC
                    int ii, jj, num_service = -1, h3 = 0, delta;
                    float h1 = 1e38f, h2 = 1e38f, cout2 = 1e38f;
                    float cveh_p = GetParam(p.cveh,  pred_type);
                    float cwait  = GetParam(p.cwait, pred_type);
                    float ctoll  = GetParam(p.ctoll, pred_type);
                    for (ii = 0; ii < lpred.services.Count; ii++)
                    {
                        delta = 0;
                        var svc = lpred.services[ii];
                        if (svc.hf > horaire
                            || reseau.nom_calendrier[svc.regime].Substring(jour, 1) == "N")
                        {
                            h1 = -1e38f; h2 = 1e38f; h3 = -1;
                            for (jj = jour - 1; jj >= Math.Max(jour - p.nb_jours, 0); jj--)
                            {
                                if (reseau.nom_calendrier[svc.regime].Substring(jj, 1) == "O"
                                    && svc.hf + (-jour + jj) * 1440f > h1
                                    && svc.hf + (-jour + jj) * 1440f < horaire)
                                { h1 = svc.hf + (-jour+jj)*1440f; h2 = -jour+jj; h3 = jj; }
                            }
                            if (h3 != -1) st.delta_service[predecesseur][ii] = h2;
                            else          delta = 1;
                        }
                        float hfD = svc.hf + st.delta_service[predecesseur][ii] * 1440f;
                        if (-hfD + horaire < max_corr)
                        {
                            float c = (svc.hf - svc.hd) * cveh_p
                                    + (-hfD + horaire) * cwait
                                    + lpred.toll * ctoll;
                            if (c < cout2 && delta < 1) { cout2 = c; num_service = ii; }
                        }
                    }
                    if (num_service != -1)
                    {
                        var svc = lpred.services[num_service];
                        float hfD = svc.hf + st.delta_service[predecesseur][num_service] * 1440f;
                        float hdD = svc.hd + st.delta_service[predecesseur][num_service] * 1440f;
                        st.service[predecesseur]    = num_service;
                        st.cout[predecesseur]       = cout2;
                        st.touche[predecesseur]     = 1;
                        st.h[predecesseur]          = hdD;
                        st.tatt[predecesseur]       = -hfD + horaire;
                        st.tatt1[predecesseur]      = -hfD + horaire;
                        st.tveh[predecesseur]       = svc.hf - svc.hd;
                        st.tcor[predecesseur]       = 0;
                        st.ncorr[predecesseur]      = 1;
                        st.l[predecesseur]          = lpred.longueur;
                        st.tmap[predecesseur]       = 0;
                        st.ttoll[predecesseur]      = lpred.toll;
                        st.pivot[predecesseur]      = -1;
                        st.turn_pivot[predecesseur] = -1;
                        st.pole[predecesseur]       = nodes[lpred.nd].i;
                        st.poleV2List[predecesseur].Clear();
                        st.poleV2List[predecesseur].Add(nodes[lpred.nd].i);
                        st.BucketInsert(predecesseur, cout2, p.param_dijkstra, p.pu, p.max_nb_buckets);
                    }
                }
            }

            // ── Boucle principale GGA ────────────────────────────────────
            int bucket_cout_max = (int)Math.Truncate(Math.Min(
                Math.Pow(p.temps_max / p.param_dijkstra, p.pu), p.max_nb_buckets - 1));

            while (st.id_bucket < st.gga_nq.Count && bucket_cout_max >= st.id_bucket)
            {
                while (st.gga_nq[st.id_bucket].Count == 0)
                {
                    st.id_bucket++;
                    if (st.id_bucket >= st.gga_nq.Count || st.id_bucket > bucket_cout_max)
                        goto fin_gga2;
                }

                // Sélectionner le pivot (meilleur coût dans le bucket)
                int pivot = -1, id_pivot = -1;
                float cout_min = 1e38f;
                var bl = st.gga_nq[st.id_bucket];
                for (int k = 0; k < bl.Count; k++)
                {
                    int idx = bl[k];
                    if (st.cout[idx] < cout_min)
                    { cout_min = st.cout[idx]; pivot = idx; id_pivot = k; }
                }
                if (pivot < 0) { st.id_bucket++; continue; }
                bl.RemoveAt(id_pivot);
                st.touche[pivot] = 3;

                var    lp2    = links[pivot];
                string ptype2 = lp2.type ?? "0";

                // Explorer les prédécesseurs du nœud .no du pivot
                for (int j = 0; j < nodes[lp2.no].pred.Count; j++)
                {
                    int  predecesseur = nodes[lp2.no].pred[j];
                    var  lpred        = links[predecesseur];
                    string pred_type  = lpred.type ?? "0";
                    string pivot_type = ptype2;

                    float penalite = 0;
                    if (p.demitours && lp2.nd == lpred.no) penalite = -1;

                    var virage = new Turn { arci = predecesseur, arcj = pivot };
                    if (nodes[lp2.no].is_intersection && turns.TryGetValue(virage, out float vpen))
                        penalite = vpen;

                    if (penalite < 0) continue;

                    float temps_correspondance = penalite > 0
                        ? penalite + GetParam(p.tboa, ptype2)
                        : GetParam(p.tboa, ptype2);
                    float max_correspondance = GetParam(p.tboa_max, ptype2);

                    st.EnsureInit(predecesseur, lpred.services.Count);

                    float cveh_r  = GetParam(p.cveh,      pred_type);
                    float cmap_r  = GetParam(p.cmap,      pred_type);
                    float ctoll_r = GetParam(p.ctoll,     pred_type);
                    float ctmap_r = GetParam(p.coef_tmap, pred_type);

                    if (st.touche[predecesseur] == 0)
                    {
                        // MAP → MAP
                        if (lpred.ligne < 0 && lp2.ligne < 0 && cmap_r > 0
                            && st.tmap[pivot] + lpred.temps < p.tmapmax)
                        {
                            bool tp = lpred.services.Count == 0;
                            if (!tp)
                            {
                                int decal = (int)Math.Floor((st.h[pivot] - penalite) / 1440f);
                                for (int kk = 0; kk < lpred.services.Count && !tp; kk++)
                                {
                                    var svc = lpred.services[kk];
                                    if (Math.Abs(decal) <= p.nb_jours
                                        && reseau.nom_calendrier[svc.regime].Substring(jour + decal, 1) == "O"
                                        && svc.hd + 1440f * decal <= st.h[pivot] - penalite
                                        && svc.hf + 1440f * decal >  st.h[pivot] - penalite)
                                        tp = true;
                                }
                            }
                            if (tp)
                            {
                                float newCout = st.cout[pivot]
                                    + (penalite + lpred.temps) * ctmap_r * cmap_r
                                    + lpred.toll * ctoll_r;
                                st.cout[predecesseur]       = newCout;
                                st.h[predecesseur]          = st.h[pivot] - lpred.temps * ctmap_r - penalite;
                                st.tatt[predecesseur]       = st.tatt[pivot];
                                st.tatt1[predecesseur]      = st.tatt1[pivot];
                                st.tveh[predecesseur]       = st.tveh[pivot];
                                st.tcor[predecesseur]       = st.tcor[pivot];
                                st.ncorr[predecesseur]      = st.ncorr[pivot];
                                st.tmap[predecesseur]       = st.tmap[pivot] + (penalite + lpred.temps) * ctmap_r;
                                st.ttoll[predecesseur]      = st.ttoll[pivot] + lpred.toll;
                                st.l[predecesseur]          = st.l[pivot] + lpred.longueur;
                                st.touche[predecesseur]     = 1;
                                st.pivot[predecesseur]      = pivot;
                                st.turn_pivot[predecesseur] = j;
                                st.pole[predecesseur]       = st.pole[pivot];
                                st.CopyPoleV2(predecesseur, pivot);
                                st.BucketInsert(predecesseur, newCout, p.param_dijkstra, p.pu, p.max_nb_buckets);
                                st.nb_pop++;
                            }
                        }
                        // MAP → TC (correspondance)
                        else if (lpred.ligne < 0 && lp2.ligne > 0 && cmap_r > 0
                                 && st.tmap[pivot] + lpred.temps < p.tmapmax)
                        {
                            bool tp = lpred.services.Count == 0;
                            if (!tp)
                            {
                                int decal = -(int)Math.Floor((st.h[pivot] - temps_correspondance) / 1440f);
                                for (int kk = 0; kk < lpred.services.Count && !tp; kk++)
                                {
                                    var svc = lpred.services[kk];
                                    if (decal <= p.nb_jours
                                        && reseau.nom_calendrier[svc.regime].Substring(jour + decal, 1) == "O"
                                        && svc.hd + 1440f * decal <= st.h[pivot] - temps_correspondance
                                        && svc.hf + 1440f * decal >  st.h[pivot] - temps_correspondance)
                                        tp = true;
                                }
                            }
                            if (tp)
                            {
                                float newCout = st.cout[pivot]
                                    + (penalite + lpred.temps) * ctmap_r * cmap_r
                                    + lpred.toll * ctoll_r;
                                st.cout[predecesseur]       = newCout;
                                st.h[predecesseur]          = st.h[pivot] - lpred.temps * ctmap_r - penalite;
                                st.tatt[predecesseur]       = st.tatt[pivot];
                                st.tatt1[predecesseur]      = st.tatt1[pivot];
                                st.tveh[predecesseur]       = st.tveh[pivot];
                                st.tcor[predecesseur]       = st.tcor[pivot] + temps_correspondance;
                                st.ncorr[predecesseur]      = st.ncorr[pivot] + 1;
                                st.tmap[predecesseur]       = st.tmap[pivot] + (penalite + lpred.temps) * ctmap_r;
                                st.ttoll[predecesseur]      = st.ttoll[pivot] + lpred.toll;
                                st.l[predecesseur]          = st.l[pivot] + lpred.longueur;
                                st.touche[predecesseur]     = 1;
                                st.pivot[predecesseur]      = pivot;
                                st.turn_pivot[predecesseur] = j;
                                st.pole[predecesseur]       = st.pole[pivot];
                                st.CopyPoleV2(predecesseur, pivot);
                                st.BucketInsert(predecesseur, newCout, p.param_dijkstra, p.pu, p.max_nb_buckets);
                                st.nb_pop++;
                            }
                        }
                        // TC → MAP (lignes différentes) ou TC → TC (correspondance)
                        else if (lpred.ligne > 0 && lp2.ligne < 0 && cveh_r > 0)
                        {
                            int ii, jj, num_service = -1, h3, delta;
                            float h1, h2, cout2 = 1e38f;
                            for (ii = 0; ii < lpred.services.Count; ii++)
                            {
                                delta = 0; h1 = 1e38f; h2 = 1e38f; h3 = -1;
                                var svc = lpred.services[ii];
                                if (svc.hf > st.h[pivot]
                                    || reseau.nom_calendrier[svc.regime].Substring(jour, 1) == "N")
                                {
                                    h1 = -1e38f;
                                    for (jj = jour - 1; jj >= Math.Max(jour - p.nb_jours, 0); jj--)
                                    {
                                        if (reseau.nom_calendrier[svc.regime].Substring(jj, 1) == "O"
                                            && svc.hf + (-jour+jj)*1440f > h1
                                            && svc.hf + (-jour+jj)*1440f < st.h[pivot])
                                        { h1 = svc.hf+(-jour+jj)*1440f; h2 = -jour+jj; h3 = jj; }
                                    }
                                    if (h3 != -1) st.delta_service[predecesseur][ii] = h2;
                                    else          delta = 1;
                                }
                                float hfD = svc.hf + st.delta_service[predecesseur][ii] * 1440f;
                                if (-hfD + st.h[pivot] < max_correspondance && delta < 1)
                                {
                                    float c = st.cout[pivot]
                                        + (svc.hf - svc.hd) * cveh_r
                                        + (-hfD + st.h[pivot]) * GetParam(p.cwait, pred_type)
                                        + lpred.toll * ctoll_r;
                                    if (c < cout2) { cout2 = c; num_service = ii; }
                                }
                            }
                            if (num_service != -1)
                            {
                                var svc  = lpred.services[num_service];
                                float hfD = svc.hf + st.delta_service[predecesseur][num_service] * 1440f;
                                float hdD = svc.hd + st.delta_service[predecesseur][num_service] * 1440f;
                                st.service[predecesseur]    = num_service;
                                st.cout[predecesseur]       = cout2;
                                st.touche[predecesseur]     = 1;
                                st.h[predecesseur]          = hdD;
                                if (st.tatt1[pivot] == 0)
                                    st.tatt1[predecesseur]  = -hfD + st.h[pivot];
                                else
                                    st.tatt1[predecesseur]  = st.tatt1[pivot];
                                st.tatt[predecesseur]       = st.tatt[pivot] - hfD + st.h[pivot];
                                st.tveh[predecesseur]       = st.tveh[pivot] + svc.hf - svc.hd;
                                st.tcor[predecesseur]       = st.tcor[pivot];
                                st.ncorr[predecesseur]      = st.ncorr[pivot];
                                st.tmap[predecesseur]       = st.tmap[pivot];
                                st.ttoll[predecesseur]      = st.ttoll[pivot] + lpred.toll;
                                st.l[predecesseur]          = st.l[pivot] + lpred.longueur;
                                st.pivot[predecesseur]      = pivot;
                                st.turn_pivot[predecesseur] = j;
                                st.pole[predecesseur]       = nodes[lpred.nd].i;
                                st.poleV2List[predecesseur].Clear();
                                st.poleV2List[predecesseur].Add(nodes[lpred.nd].i);
                                st.BucketInsert(predecesseur, cout2, p.param_dijkstra, p.pu, p.max_nb_buckets);
                                st.nb_pop++;
                            }
                        }
                        // TC → TC (lignes différentes, correspondance)
                        else if (lpred.ligne > 0 && lp2.ligne > 0
                                 && lpred.ligne != lp2.ligne && cveh_r > 0)
                        {
                            int ii, jj, num_service = -1, h3, delta;
                            float h1, h2, cout2 = 1e38f;
                            for (ii = 0; ii < lpred.services.Count; ii++)
                            {
                                delta = 0; h1 = 1e38f; h2 = 1e38f; h3 = -1;
                                var svc = lpred.services[ii];
                                if (svc.hf + temps_correspondance > st.h[pivot]
                                    || reseau.nom_calendrier[svc.regime].Substring(jour, 1) == "N")
                                {
                                    h1 = -1e38f;
                                    for (jj = jour - 1; jj >= Math.Max(jour - p.nb_jours, 0); jj--)
                                    {
                                        if (reseau.nom_calendrier[svc.regime].Substring(jj, 1) == "O"
                                            && svc.hf + (-jour+jj)*1440f > h1
                                            && svc.hf + (-jour+jj)*1440f + temps_correspondance < st.h[pivot])
                                        { h1 = svc.hf+(-jour+jj)*1440f; h2 = -jour+jj; h3 = jj; }
                                    }
                                    if (h3 != -1)
                                    {
                                        if (st.delta_service[predecesseur][ii] > h2 || st.touche[predecesseur] == 0)
                                            st.delta_service[predecesseur][ii] = h2;
                                    }
                                    else delta = 1;
                                }
                                float hfD = svc.hf + st.delta_service[predecesseur][ii] * 1440f;
                                if (hfD + max_correspondance >= st.h[pivot]
                                    && hfD + temps_correspondance <= st.h[pivot]
                                    && delta < 1)
                                {
                                    float c = st.cout[pivot]
                                        + (svc.hf - svc.hd) * cveh_r
                                        + (-hfD + st.h[pivot] - temps_correspondance) * GetParam(p.cwait, pred_type)
                                        + temps_correspondance * GetParam(p.cboa, pivot_type)
                                        + lpred.toll * ctoll_r;
                                    if (c < cout2) { cout2 = c; num_service = ii; }
                                }
                            }
                            if (num_service != -1)
                            {
                                float hfD = lpred.services[num_service].hf
                                          + st.delta_service[predecesseur][num_service] * 1440f;
                                float hdD = lpred.services[num_service].hd
                                          + st.delta_service[predecesseur][num_service] * 1440f;
                                st.service[predecesseur]    = num_service;
                                st.cout[predecesseur]       = cout2;
                                st.touche[predecesseur]     = 1;
                                st.h[predecesseur]          = hdD;
                                if (st.tatt1[pivot] == 0)
                                    st.tatt1[predecesseur]  = -hfD - st.delta_service[predecesseur][num_service]*1440f + st.h[pivot];
                                else
                                    st.tatt1[predecesseur]  = st.tatt1[pivot];
                                st.tatt[predecesseur]       = st.tatt[pivot] - hfD + st.h[pivot];
                                st.tveh[predecesseur]       = st.tveh[pivot] + lpred.services[num_service].hf - lpred.services[num_service].hd;
                                st.tcor[predecesseur]       = st.tcor[pivot];
                                st.ncorr[predecesseur]      = st.ncorr[pivot];
                                st.tmap[predecesseur]       = st.tmap[pivot];
                                st.ttoll[predecesseur]      = st.ttoll[pivot] + lpred.toll;
                                st.l[predecesseur]          = st.l[pivot] + lpred.longueur;
                                st.pivot[predecesseur]      = pivot;
                                st.turn_pivot[predecesseur] = j;
                                st.pole[predecesseur]       = nodes[lpred.nd].i;
                                st.poleV2List[predecesseur].Clear();
                                st.poleV2List[predecesseur].Add(nodes[lpred.nd].i);
                                st.poleV2List[predecesseur].Add(nodes[lpred.nd].i);
                                st.BucketInsert(predecesseur, cout2, p.param_dijkstra, p.pu, p.max_nb_buckets);
                                st.nb_pop++;
                            }
                        }
                    }
                    else if (st.touche[predecesseur] == 1 || st.touche[predecesseur] == 2)
                    {
                        // Éléments déjà touchés — mise à jour si meilleur coût

                        // MAP → MAP
                        if (lpred.ligne < 0 && lp2.ligne < 0 && cmap_r > 0
                            && st.tmap[pivot] + lpred.temps < p.tmapmax
                            && st.cout[predecesseur] > st.cout[pivot])
                        {
                            bool tp = lpred.services.Count == 0;
                            if (!tp)
                            {
                                int decal = (int)Math.Floor((st.h[pivot] - penalite) / 1440f);
                                for (int kk = 0; kk < lpred.services.Count && !tp; kk++)
                                {
                                    var svc = lpred.services[kk];
                                    if (Math.Abs(decal) <= p.nb_jours
                                        && reseau.nom_calendrier[svc.regime].Substring(jour+decal,1)=="O"
                                        && svc.hd+1440f*decal <= st.h[pivot]-penalite
                                        && svc.hf+1440f*decal >  st.h[pivot]-penalite)
                                        tp = true;
                                }
                            }
                            if (tp)
                            {
                                float newCout = st.cout[pivot]
                                    + (penalite + lpred.temps) * ctmap_r * cmap_r
                                    + lpred.toll * ctoll_r;
                                if (st.cout[predecesseur] > newCout)
                                {
                                    int bOld = (int)Math.Truncate(Math.Min(
                                        Math.Pow(st.cout[predecesseur]/p.param_dijkstra, p.pu), p.max_nb_buckets-1));
                                    if (bOld < st.gga_nq.Count)
                                        st.gga_nq[bOld].Remove(predecesseur);
                                    st.cout[predecesseur]       = newCout;
                                    st.h[predecesseur]          = st.h[pivot] - lpred.temps * ctmap_r - penalite;
                                    st.tatt[predecesseur]       = st.tatt[pivot];
                                    st.tatt1[predecesseur]      = st.tatt1[pivot];
                                    st.tveh[predecesseur]       = st.tveh[pivot];
                                    st.tcor[predecesseur]       = st.tcor[pivot];
                                    st.ncorr[predecesseur]      = st.ncorr[pivot];
                                    st.tmap[predecesseur]       = st.tmap[pivot] + (penalite+lpred.temps)*ctmap_r;
                                    st.ttoll[predecesseur]      = st.ttoll[pivot] + lpred.toll;
                                    st.l[predecesseur]          = st.l[pivot] + lpred.longueur;
                                    st.touche[predecesseur]     = 2;
                                    st.pivot[predecesseur]      = pivot;
                                    st.turn_pivot[predecesseur] = j;
                                    st.pole[predecesseur]       = nodes[lpred.nd].i;
                                    st.CopyPoleV2(predecesseur, pivot);
                                    st.BucketInsert(predecesseur, newCout, p.param_dijkstra, p.pu, p.max_nb_buckets);
                                    st.nb_pop++;
                                }
                            }
                        }
                        // TC même ligne
                        else if (lpred.ligne > 0 && lp2.ligne > 0
                                 && lpred.ligne == lp2.ligne && cveh_r > 0
                                 && st.cout[predecesseur] > st.cout[pivot])
                        {
                            int num_service = -1;
                            for (int ii = 0; ii < lpred.services.Count; ii++)
                            {
                                var svc = lpred.services[ii];
                                if (st.service[pivot] >= 0
                                    && svc.numero == lp2.services[st.service[pivot]].numero
                                    && svc.hf <= lp2.services[st.service[pivot]].hd)
                                    num_service = ii;
                            }
                            if (num_service != -1)
                            {
                                var svc = lpred.services[num_service];
                                float hfD = svc.hf + lp2.services[st.service[pivot] >= 0 ? st.service[pivot] : 0].delta * 1440f;
                                float hdD = svc.hd + lp2.services[st.service[pivot] >= 0 ? st.service[pivot] : 0].delta * 1440f;
                                if (hfD <= st.h[pivot])
                                {
                                    float newCout = st.cout[pivot]
                                        + (-hdD + st.h[pivot]) * cveh_r
                                        + lpred.toll * ctoll_r;
                                    if (st.cout[predecesseur] > newCout
                                        && (st.service[predecesseur] < 0
                                            || lpred.services[st.service[predecesseur]].hf
                                               <= lp2.services[st.service[pivot] >= 0 ? st.service[pivot] : 0].hd))
                                    {
                                        int bOld = (int)Math.Truncate(Math.Min(
                                            Math.Pow(st.cout[predecesseur]/p.param_dijkstra, p.pu), p.max_nb_buckets-1));
                                        if (bOld < st.gga_nq.Count)
                                            st.gga_nq[bOld].Remove(predecesseur);
                                        st.service[predecesseur]    = num_service;
                                        st.delta_service[predecesseur][num_service]
                                            = st.service[pivot] >= 0
                                              ? lp2.services[st.service[pivot]].delta : 0;
                                        st.touche[predecesseur]     = 2;
                                        st.cout[predecesseur]       = newCout;
                                        st.h[predecesseur]          = hdD;
                                        st.tatt[predecesseur]       = st.tatt[pivot];
                                        st.tatt1[predecesseur]      = st.tatt1[pivot];
                                        st.tveh[predecesseur]       = st.tveh[pivot];
                                        st.tcor[predecesseur]       = st.tcor[pivot];
                                        st.ncorr[predecesseur]      = st.ncorr[pivot];
                                        st.tmap[predecesseur]       = st.tmap[pivot];
                                        st.ttoll[predecesseur]      = st.ttoll[pivot] + lpred.toll;
                                        st.l[predecesseur]          = st.l[pivot] + lpred.longueur;
                                        st.pivot[predecesseur]      = pivot;
                                        st.turn_pivot[predecesseur] = j;
                                        st.pole[predecesseur]       = st.pole[pivot];
                                        st.CopyPoleV2(predecesseur, pivot);
                                        st.BucketInsert(predecesseur, newCout, p.param_dijkstra, p.pu, p.max_nb_buckets);
                                        st.nb_pop++;
                                    }
                                }
                            }
                        }
                        // TC lignes différentes → MAP
                        else if (lpred.ligne > 0 && lp2.ligne < 0 && cveh_r > 0
                                 && st.cout[predecesseur] > st.cout[pivot])
                        {
                            int ii, jj, num_service = -1, h3, delta;
                            float h1, h2, cout2 = 1e38f;
                            for (ii = 0; ii < lpred.services.Count; ii++)
                            {
                                delta = 0; h1 = 1e38f; h2 = 1e38f; h3 = -1;
                                var svc = lpred.services[ii];
                                if (svc.hf + temps_correspondance > st.h[pivot]
                                    || reseau.nom_calendrier[svc.regime].Substring(jour,1) == "N")
                                {
                                    h1 = -1e38f;
                                    for (jj = jour-1; jj >= Math.Max(jour-p.nb_jours,0); jj--)
                                    {
                                        if (reseau.nom_calendrier[svc.regime].Substring(jj,1) == "O"
                                            && svc.hf+(-jour+jj)*1440f > h1
                                            && svc.hf+(-jour+jj)*1440f < st.h[pivot])
                                        { h1 = svc.hf+(-jour+jj)*1440f; h2 = -jour+jj; h3 = jj; }
                                    }
                                    if (h3 != -1)
                                    {
                                        if (st.delta_service[predecesseur][ii] > h2 || st.touche[predecesseur] == 0)
                                            st.delta_service[predecesseur][ii] = h2;
                                    }
                                    else delta = 1;
                                }
                                float hfD = svc.hf + st.delta_service[predecesseur][ii] * 1440f;
                                if (hfD + max_correspondance >= st.h[pivot]
                                    && hfD + temps_correspondance <= st.h[pivot] && delta < 1)
                                {
                                    float c = st.cout[pivot]
                                        + (svc.hf - svc.hd) * cveh_r
                                        + (-hfD + st.h[pivot] - temps_correspondance) * GetParam(p.cwait, pred_type)
                                        + lpred.toll * ctoll_r;
                                    if (c < cout2) { cout2 = c; num_service = ii; }
                                }
                            }
                            if (num_service != -1 && st.cout[predecesseur] > cout2)
                            {
                                float hfD = lpred.services[num_service].hf
                                          + st.delta_service[predecesseur][num_service]*1440f;
                                float hdD = lpred.services[num_service].hd
                                          + st.delta_service[predecesseur][num_service]*1440f;
                                int bOld = (int)Math.Truncate(Math.Min(
                                    Math.Pow(st.cout[predecesseur]/p.param_dijkstra, p.pu), p.max_nb_buckets-1));
                                if (bOld < st.gga_nq.Count)
                                    st.gga_nq[bOld].Remove(predecesseur);
                                st.service[predecesseur]    = num_service;
                                st.cout[predecesseur]       = cout2;
                                st.touche[predecesseur]     = 2;
                                st.h[predecesseur]          = hdD;
                                if (st.tatt1[pivot] == 0)
                                    st.tatt1[predecesseur]  = -hfD + st.h[pivot];
                                else
                                    st.tatt1[predecesseur]  = st.tatt1[pivot];
                                st.tatt[predecesseur]       = st.tatt[pivot] - hfD + st.h[pivot];
                                st.tveh[predecesseur]       = st.tveh[pivot] + lpred.services[num_service].hf - lpred.services[num_service].hd;
                                st.tcor[predecesseur]       = st.tcor[pivot];
                                st.ncorr[predecesseur]      = st.ncorr[pivot];
                                st.tmap[predecesseur]       = st.tmap[pivot];
                                st.ttoll[predecesseur]      = st.ttoll[pivot] + lpred.toll;
                                st.l[predecesseur]          = st.l[pivot] + lpred.longueur;
                                st.pivot[predecesseur]      = pivot;
                                st.turn_pivot[predecesseur] = j;
                                st.pole[predecesseur]       = nodes[lpred.nd].i;
                                st.poleV2List[predecesseur].Clear();
                                st.poleV2List[predecesseur].Add(nodes[lpred.nd].i);
                                st.poleV2List[predecesseur].Add(nodes[lpred.nd].i);
                                st.BucketInsert(predecesseur, cout2, p.param_dijkstra, p.pu, p.max_nb_buckets);
                                st.nb_pop++;
                            }
                        }
                    }
                }
            }
            fin_gga2:
            return true;
        }

        // ══════════════════════════════════════════════════════════════════
        //  Extraction des résultats depuis le DijkstraState
        //  [OPT-7] StringBuilder pour toutes les lignes de sortie
        //  [OPT-5] GetPoleV2String uniquement à la sortie
        // ══════════════════════════════════════════════════════════════════
        static ResultatOD ExtraireResultat(
            network reseau, Param_affectation_horaire p,
            DijkstraState st, PaireOD paire,
            HashSet<string> filtre, bool dijkstraOk)
        {
            var res = new ResultatOD
            {
                numod          = paire.numod,
                p              = paire.p,
                q              = paire.q,
                libod          = paire.libod,
                od             = paire.od,
                arrivee_link   = -1,
                accumulations  = new List<(int,float,int,float,float,float,float,float)>(),
                lignes_temps   = new List<string>(),
                lignes_chemins = new List<string>(),
                lignes_noeuds  = new List<string>(),
                lignes_isoles  = new List<string>(),
            };

            if (!dijkstraOk) return res;

            // ── Trouver le lien d'arrivée ────────────────────────────────
            int arrivee = -1; double cout_fin = 1e38;
            if (paire.sens == 1)
            {
                // Sens 1 : meilleur arc entrant en q (pred de q)
                if (reseau.numnoeud.TryGetValue(paire.q, out int nodeQ))
                    foreach (int pred in reseau.nodes[nodeQ].pred)
                        if (st.EstAtteint(pred) && st.cout[pred] < cout_fin)
                        { arrivee = pred; cout_fin = st.cout[pred]; }
            }
            else
            {
                // Sens 2 : meilleur arc sortant de p (succ de p)
                if (reseau.numnoeud.TryGetValue(paire.p, out int nodeP2))
                    foreach (int succ in reseau.nodes[nodeP2].succ)
                        if (st.EstAtteint(succ) && st.cout[succ] < cout_fin)
                        { arrivee = succ; cout_fin = st.cout[succ]; }
            }
            res.arrivee_link = arrivee;

            // ── Lignes isolées (liens non atteints) ──────────────────────
            if (p.sortie_isoles)
            {
                for (int i = 0; i < reseau.links.Count; i++)
                {
                    if (!st.EstAtteint(i) && (filtre.Count == 0 || filtre.Contains(reseau.links[i].type ?? "")))
                    {
                        var sb = new StringBuilder();
                        sb.Append(reseau.nodes[reseau.links[i].no].i)
                          .Append('-').Append(reseau.nodes[reseau.links[i].nd].i)
                          .Append(';').Append(reseau.links[i].ligne.ToString("0"))
                          .Append(';').Append(i.ToString("0"));
                        res.lignes_isoles.Add(sb.ToString());
                    }
                }
            }

            if (arrivee < 0) return res;

            // ── Ligne OD ─────────────────────────────────────────────────
            string itineraire = "";
            {
                int cur2 = arrivee;
                string[] param2 = {"|"};
                if (reseau.links[cur2].texte != null)
                {
                    var lc = reseau.links[cur2].texte.Split(param2, StringSplitOptions.RemoveEmptyEntries);
                    itineraire = lc.Length > 0 ? lc[0] : "MAP";
                }
                else itineraire = "MAP";

                int tmp = st.pivot[cur2];
                while (tmp >= 0)
                {
                    if (reseau.links[cur2].ligne != reseau.links[tmp].ligne)
                    {
                        string[] lc2 = null;
                        if (reseau.links[tmp].texte != null)
                            lc2 = reseau.links[tmp].texte.Split(param2, StringSplitOptions.RemoveEmptyEntries);
                        itineraire = (lc2 != null && lc2.Length > 0 ? lc2[0] : "MAP") + "|" + itineraire;
                    }
                    cur2 = tmp;
                    tmp  = st.pivot[cur2];
                }
            }

            var sb0 = new StringBuilder(300);
            float heureo = paire.sens == 1 ? paire.horaire    : st.h[arrivee];
            float heured = paire.sens == 1 ? st.h[arrivee]    : paire.horaire;
            float temps  = heured - heureo;
            sb0.Append(paire.libod).Append(';').Append(paire.p).Append(';').Append(paire.q)
              .Append(';').Append(paire.jour.ToString("0.000"))
              .Append(';').Append(heureo.ToString("0.000"))
              .Append(';').Append(heured.ToString("0.000"))
              .Append(';').Append(temps.ToString("0.000"))
              .Append(';').Append(st.tveh[arrivee].ToString("0.000"))
              .Append(';').Append(st.tmap[arrivee].ToString("0.000"))
              .Append(';').Append(st.tatt[arrivee].ToString("0.000"))
              .Append(';').Append(st.tcor[arrivee].ToString("0.000"))
              .Append(';').Append(st.ncorr[arrivee].ToString("0"))
              .Append(';').Append(st.tatt1[arrivee].ToString("0.000"))
              .Append(';').Append(st.cout[arrivee].ToString("0.000"))
              .Append(';').Append(st.l[arrivee].ToString("0.000"))
              .Append(';').Append(st.pole[arrivee])
              .Append(';').Append(paire.od.ToString("0.00"))
              .Append(';').Append(itineraire)
              .Append(';').Append(st.nb_pop)
              .Append(';').Append(st.ttoll[arrivee].ToString("0.000"));
            res.ligne_od = sb0.ToString();

            // ── Collecter les accumulations + lignes chemins ─────────────
            int cur = arrivee;
            while (cur >= 0)
            {
                var lien   = reseau.links[cur];
                int svcIdx = st.service[cur];
                bool isFirst    = (st.pivot[cur] == -1);
                bool lineChange = !isFirst && lien.ligne != reseau.links[st.pivot[cur]].ligne;

                // Accumuler boai au premier lien TC ou changement de ligne
                float boaiVal  = (lien.ligne > 0 && (isFirst || lineChange)) ? paire.od : 0f;
                float boatVal  = boaiVal;
                // Accumuler alij au dernier lien TC avant changement (= pivot de l'arc courant)
                float alijVal  = 0f, alitVal = 0f;
                if (lien.ligne > 0 && lineChange && st.pivot[cur] >= 0
                    && reseau.links[st.pivot[cur]].ligne > 0)
                {
                    alijVal = paire.od; alitVal = paire.od;
                }

                res.accumulations.Add((cur, paire.od, svcIdx,
                    svcIdx >= 0 ? paire.od : 0f,
                    boaiVal, boatVal, alijVal, alitVal));

                // ── Ligne _chemins ──────────────────────────────────────
                if (p.sortie_chemins)
                {
                    var sb2 = new StringBuilder(250);
                    sb2.Append(paire.libod).Append(';').Append(paire.p).Append(';').Append(paire.q)
                       .Append(';').Append(paire.jour.ToString("0")).Append(';').Append(paire.horaire.ToString("0.000"))
                       .Append(';').Append(reseau.nodes[lien.no].i)
                       .Append(';').Append(reseau.nodes[lien.nd].i)
                       .Append(';').Append(reseau.nodes[lien.no].i).Append('-').Append(reseau.nodes[lien.nd].i)
                       .Append(';').Append(lien.ligne.ToString("0"))
                       .Append(';');
                    if (svcIdx >= 0) sb2.Append(lien.services[svcIdx].numero.ToString("0"));
                    else             sb2.Append("-1");
                    float tempsChemin = paire.sens == 1
                        ? st.h[cur] - paire.horaire
                        : paire.horaire - st.h[cur];
                    sb2.Append(';').Append(tempsChemin.ToString("0.000"))
                       .Append(';').Append(st.h[cur].ToString("0.000"))
                       .Append(';').Append(st.tveh[cur].ToString("0.000"))
                       .Append(';').Append(st.tmap[cur].ToString("0.000"))
                       .Append(';').Append(st.tatt[cur].ToString("0.000"))
                       .Append(';').Append(st.tcor[cur].ToString("0.000"))
                       .Append(';').Append(st.ncorr[cur].ToString("0"))
                       .Append(';').Append(st.tatt1[cur].ToString("0.000"))
                       .Append(';').Append(st.cout[cur].ToString("0.000"))
                       .Append(';').Append(st.l[cur].ToString("0.000"))
                       .Append(';').Append(st.pole[cur])
                       .Append(';').Append(paire.od.ToString("0.00"));
                    // boai / alij du service (réinitialisés dans l'original après écriture)
                    if (lien.ligne > 0 && svcIdx >= 0)
                    {
                        sb2.Append(';').Append(boaiVal.ToString("0.000"))
                           .Append(';').Append(alijVal.ToString("0.000"));
                    }
                    else sb2.Append(";0.000;0.000");
                    sb2.Append(';').Append(lien.texte ?? "")
                       .Append(';').Append(lien.type ?? "")
                       .Append(';').Append(st.ttoll[cur].ToString("0.000"));
                    res.lignes_chemins.Add(sb2.ToString());
                }

                cur = st.pivot[cur];
            }

            // ── Alij sur le lien d'arrivée ───────────────────────────────
            {
                var lienArr = reseau.links[arrivee];
                int svcArr  = st.service[arrivee];
                if (lienArr.ligne > 0 && svcArr >= 0)
                {
                    // Marquer l'accumulation alij déjà dans la boucle ci-dessus
                    // (arrivee = dernier nœud, pas de pivot TC après → alij ajouté directement)
                    res.accumulations[0] = (
                        res.accumulations[0].linkIdx,
                        res.accumulations[0].volau,
                        res.accumulations[0].svcIdx,
                        res.accumulations[0].volauSvc,
                        res.accumulations[0].boai,
                        res.accumulations[0].boatSvc,
                        paire.od,   // alij
                        paire.od    // alitSvc
                    );
                }
            }

            // ── Lignes _temps (sortie_temps 1-3) ─────────────────────────
            int sort_temps = paire.a_params_specifiques ? paire.sortie_temps : p.sortie_temps;
            if (sort_temps > 0 && sort_temps < 4)
            {
                for (int i = 0; i < reseau.links.Count; i++)
                {
                    if (!st.EstAtteint(i)) continue;
                    var lien = reseau.links[i];
                    if (lien.ligne >= 0 && sort_temps != 2) continue;
                    if (st.cout[i] > p.temps_max) continue;
                    if (filtre.Count > 0 && !filtre.Contains(lien.type ?? "")) continue;

                    var sb2 = new StringBuilder(200);
                    if (sort_temps == 3 && !p.sortie_noeuds)
                    {
                        sb2.Append(paire.p)
                           .Append(';').Append(reseau.nodes[lien.no].i).Append('-').Append(reseau.nodes[lien.nd].i)
                           .Append(';').Append((-paire.horaire + st.h[i]).ToString("0.000"))
                           .Append(';').Append(st.tatt1[i].ToString("0.000"))
                           .Append(';').Append(paire.od.ToString("0.000"));
                    }
                    else if (sort_temps < 3)
                    {
                        float ti = lien.ligne < 0
                            ? paire.horaire - (st.h[i] + lien.temps * p.coef_tmap.GetValueOrDefault(lien.type ?? "0", p.coef_tmap.GetValueOrDefault("0", 1f)))
                            : paire.horaire - (st.h[i] + (st.service[i] >= 0 ? lien.services[st.service[i]].hf - lien.services[st.service[i]].hd : 0f));
                        sb2.Append(paire.libod).Append(';').Append(paire.p)
                           .Append(';').Append(reseau.nodes[lien.no].i).Append('-').Append(reseau.nodes[lien.nd].i)
                           .Append(';').Append(lien.ligne.ToString("0"))
                           .Append(';').Append(i.ToString("0"))
                           .Append(';').Append(paire.jour.ToString("0"))
                           .Append(';').Append(paire.horaire.ToString("0.000"))
                           .Append(';').Append(st.h[i].ToString("0.000"))
                           .Append(';').Append((-paire.horaire + st.h[i]).ToString("0.000"))
                           .Append(';').Append(st.tveh[i].ToString("0.000"))
                           .Append(';').Append(st.tmap[i].ToString("0.000"))
                           .Append(';').Append(st.tatt[i].ToString("0.000"))
                           .Append(';').Append(st.tcor[i].ToString("0.000"))
                           .Append(';').Append(st.ncorr[i].ToString("0"))
                           .Append(';').Append(st.tatt1[i].ToString("0.000"))
                           .Append(';').Append(st.cout[i].ToString("0.000"))
                           .Append(';').Append(st.l[i].ToString("0.000"))
                           .Append(';').Append(st.pole[i])
                           .Append(';').Append(paire.od.ToString("0.00"))
                           .Append(';').Append(st.pivot[i].ToString("0"))
                           .Append(';').Append(lien.type ?? "")
                           .Append(';').Append(st.ttoll[i].ToString("0.000"))
                           .Append(';').Append(ti.ToString("0.000"));
                    }
                    res.lignes_temps.Add(sb2.ToString());
                }
            }

            // ── Lignes _noeuds ────────────────────────────────────────────
            if (p.sortie_noeuds)
            {
                foreach (var n in reseau.nodes)
                {
                    float tmax2 = 1e38f; int which_tmax = -1; string type_arc = "";
                    foreach (int s in n.pred)
                    {
                        var troncon = reseau.links[s];
                        if (st.EstAtteint(s) && st.cout[s] <= tmax2
                            && (troncon.ligne <= 0 || sort_temps == 2))
                        {
                            tmax2      = st.cout[s];
                            which_tmax = s;
                            type_arc   = troncon.type ?? "";
                        }
                    }
                    if (which_tmax < 0 || tmax2 > p.temps_max) continue;
                    if (filtre.Count > 0 && !filtre.Contains(type_arc)) continue;

                    var sb3 = new StringBuilder(250);
                    if (sort_temps == 3)
                    {
                        sb3.Append(paire.p).Append(';').Append(n.i)
                           .Append(';').Append((-paire.horaire + st.h[which_tmax]).ToString("0.000"))
                           .Append(';').Append(st.tatt1[which_tmax].ToString("0.000"))
                           .Append(';').Append(paire.od.ToString("0.000"));
                    }
                    else
                    {
                        sb3.Append(paire.libod).Append(';').Append(paire.p).Append(';').Append(paire.q)
                           .Append(';').Append(paire.jour.ToString("0.000"))
                           .Append(';').Append(n.i)
                           .Append(';').Append(paire.horaire.ToString("0.000"))
                           .Append(';').Append(st.h[which_tmax].ToString("0.000"))
                           .Append(';').Append((-paire.horaire + st.h[which_tmax]).ToString("0.000"))
                           .Append(';').Append(st.tveh[which_tmax].ToString("0.000"))
                           .Append(';').Append(st.tmap[which_tmax].ToString("0.000"))
                           .Append(';').Append(st.tatt[which_tmax].ToString("0.000"))
                           .Append(';').Append(st.tcor[which_tmax].ToString("0.000"))
                           .Append(';').Append(st.ncorr[which_tmax].ToString("0"))
                           .Append(';').Append(st.tatt1[which_tmax].ToString("0.000"))
                           .Append(';').Append(st.cout[which_tmax].ToString("0.000"))
                           .Append(';').Append(st.l[which_tmax].ToString("0.000"))
                           .Append(';').Append(st.pole[which_tmax])
                           .Append(';').Append(st.ttoll[which_tmax].ToString("0.000"))
                           .Append(';').Append(paire.od.ToString("0.000"));
                        if (p.sortie_stops)
                            sb3.Append(';').Append(st.GetPoleV2String(which_tmax));
                        else
                            sb3.Append(';');
                    }
                    res.lignes_noeuds.Add(sb3.ToString());
                }
            }

            // ── Ligne _detour (sens==1 uniquement) ───────────────────────
            if (sort_temps == 0 && paire.sens == 1 && reseau.numnoeud.ContainsKey(paire.p))
            {
                double som_detour = 0, nb_detour = 0, som_oiseau = 0;
                var    nodeP      = reseau.nodes[reseau.numnoeud[paire.p]];
                for (int liIdx = 0; liIdx < reseau.links.Count; liIdx++)
                {
                    var li = reseau.links[liIdx];
                    double d_oiseau = Math.Sqrt(
                        Math.Pow(nodeP.x - reseau.nodes[li.nd].x, 2) +
                        Math.Pow(nodeP.y - reseau.nodes[li.nd].y, 2));
                    double d_link = Math.Sqrt(
                        Math.Pow(reseau.nodes[li.no].x - reseau.nodes[li.nd].x, 2) +
                        Math.Pow(reseau.nodes[li.no].y - reseau.nodes[li.nd].y, 2));
                    if (d_oiseau > 500 && d_oiseau - d_link <= 500
                        && nodeP.x > 0 && nodeP.y > 0
                        && reseau.nodes[li.nd].x > 0 && reseau.nodes[li.nd].y > 0)
                    {
                        if (st.EstAtteint(liIdx) && st.h[liIdx] > 0)
                        {
                            som_detour += st.h[liIdx];
                            som_oiseau += d_oiseau;
                            nb_detour++;
                        }
                    }
                }
                res.ligne_detour = paire.p + ";" + som_detour + ";" + som_oiseau + ";" + nb_detour;
            }

            return res;
        }

        // ══════════════════════════════════════════════════════════════════
        //  [PAR-4] Accumulations séquentielles — sans lock
        // ══════════════════════════════════════════════════════════════════
        static void AppliquerAccumulations(
            network reseau, ConcurrentBag<ResultatOD> resultats)
        {
            foreach (var res in resultats)
            {
                if (res.accumulations == null) continue;
                foreach (var (linkIdx, volau, svcIdx, volauSvc,
                              boai, boatSvc, alij, alitSvc) in res.accumulations)
                {
                    reseau.links[linkIdx].volau += volau;
                    if (svcIdx >= 0 && svcIdx < reseau.links[linkIdx].services.Count)
                    {
                        var svc = reseau.links[linkIdx].services[svcIdx];
                        svc.volau += volauSvc;
                        svc.boai  += boai;
                        svc.boat  += boatSvc;
                        svc.alij  += alij;
                        svc.alit  += alitSvc;
                    }
                    reseau.links[linkIdx].boai += boai;
                    reseau.links[linkIdx].alij += alij;
                }
            }
        }

        // ══════════════════════════════════════════════════════════════════
        //  Écriture sorties réseau (liens, services, turns) — inchangée
        // ══════════════════════════════════════════════════════════════════
        static void EcrireSortiesReseau(etude projet,
            Param_affectation_horaire aff_hor,
            Dictionary<Turn,float> transfers,
            StreamWriter fich_log)
        {
            network reseau = projet.reseaux[projet.reseau_actif];

            // ── Fichier _aff.txt (liens avec volau > 0) ──────────────────────
            using (var fich_result = new StreamWriter(aff_hor.nom_sortie + "_aff.txt", false, Encoding.UTF8))
            {
                fich_result.WriteLine("i;j;ligne;volau;boai;alij;texte;type;toll");
                for (int i = 0; i < reseau.links.Count; i++)
                {
                    var lien = reseau.links[i];
                    if (lien.volau > 0 || lien.boai > 0 || lien.alij > 0)
                    {
                        var sb = new StringBuilder();
                        sb.Append(reseau.nodes[lien.no].i);
                        sb.Append(';').Append(reseau.nodes[lien.nd].i);
                        sb.Append(';').Append(lien.ligne.ToString("0"));
                        sb.Append(';').Append(lien.volau.ToString("0.00", Formats.Inv));
                        sb.Append(';').Append(lien.boai.ToString("0.00",  Formats.Inv));
                        sb.Append(';').Append(lien.alij.ToString("0.00",  Formats.Inv));
                        sb.Append(';').Append(lien.texte);
                        sb.Append(';').Append(lien.type);
                        sb.Append(';').Append(lien.toll.ToString("0.000", Formats.Inv));
                        fich_result.WriteLine(sb);
                    }
                }
            }

            // ── Fichier _services.txt ─────────────────────────────────────────
            if (aff_hor.sortie_services)
            {
                using var fich_services = new StreamWriter(aff_hor.nom_sortie + "_services.txt", false, Encoding.UTF8);
                fich_services.WriteLine("i;j;ligne;service;hd;hf;regime;volau;boia;alij;texte;type");
                for (int i = 0; i < reseau.links.Count; i++)
                {
                    var lien = reseau.links[i];
                    for (int j = 0; j < lien.services.Count; j++)
                    {
                        var svc = lien.services[j];
                        if (svc.volau > 0)
                        {
                            var sb = new StringBuilder();
                            sb.Append(reseau.nodes[lien.no].i);
                            sb.Append(';').Append(reseau.nodes[lien.nd].i);
                            sb.Append(';').Append(lien.ligne.ToString("0"));
                            sb.Append(';').Append(svc.numero);
                            sb.Append(';').Append(svc.hd.ToString(Formats.Inv));
                            sb.Append(';').Append(svc.hf.ToString(Formats.Inv));
                            sb.Append(';').Append(reseau.nom_calendrier[svc.regime]);
                            sb.Append(';').Append(svc.volau.ToString("0.00", Formats.Inv));
                            sb.Append(';').Append(svc.boat.ToString("0.00",  Formats.Inv));
                            sb.Append(';').Append(svc.alit.ToString("0.00",  Formats.Inv));
                            sb.Append(';').Append(lien.texte);
                            sb.Append(';').Append(lien.type);
                            fich_services.WriteLine(sb);
                        }
                    }
                }
            }

            // ── Fichier _transferts.txt ───────────────────────────────────────
            if (aff_hor.sortie_turns)
            {
                using var fich_turns = new StreamWriter(aff_hor.nom_sortie + "_transferts.txt", false, Encoding.UTF8);
                fich_turns.WriteLine("j;i;lignei;k;lignek;textei;textek;volau");
                foreach (Turn virage in transfers.Keys)
                {
                    if (transfers[virage] > 0)
                    {
                        var sb = new StringBuilder();
                        sb.Append(reseau.nodes[reseau.links[virage.arci].nd].i);
                        sb.Append(';').Append(reseau.nodes[reseau.links[virage.arci].no].i);
                        sb.Append(';').Append(reseau.links[virage.arci].ligne);
                        sb.Append(';').Append(reseau.nodes[reseau.links[virage.arcj].nd].i);
                        sb.Append(';').Append(reseau.links[virage.arcj].ligne);
                        sb.Append(';').Append(reseau.links[virage.arci].texte);
                        sb.Append(';').Append(reseau.links[virage.arcj].texte);
                        sb.Append(';').Append(transfers[virage].ToString(Formats.Inv));
                        fich_turns.WriteLine(sb);
                    }
                }
            }
        }

        // ══════════════════════════════════════════════════════════════════
        //  [PAR-3] Writer asynchrone depuis un Channel
        // ══════════════════════════════════════════════════════════════════
        static Task EcrireDepuisChannel(ChannelReader<string> reader, StreamWriter writer)
            => Task.Run(async () =>
            {
                await foreach (var line in reader.ReadAllAsync())
                    writer.WriteLine(line);
                writer.Flush();
            });

        // ══════════════════════════════════════════════════════════════════
        //  Fusion des paramètres globaux avec les overrides par paire O-D
        // ══════════════════════════════════════════════════════════════════
        static Param_affectation_horaire FusionnerParametres(
            Param_affectation_horaire global, PaireOD od)
        {
            // Crée un clone léger avec les valeurs overridées par la paire
            var p = global.Clone();
            if (od.cveh      != null) p.cveh      = od.cveh;
            if (od.cwait     != null) p.cwait     = od.cwait;
            if (od.cmap      != null) p.cmap      = od.cmap;
            if (od.cboa      != null) p.cboa      = od.cboa;
            if (od.coef_tmap != null) p.coef_tmap = od.coef_tmap;
            if (od.tboa      != null) p.tboa      = od.tboa;
            if (od.tboa_max  != null) p.tboa_max  = od.tboa_max;
            if (od.ctoll     != null) p.ctoll     = od.ctoll;
            p.sortie_chemins = od.sortie_chemins;
            p.sortie_temps   = od.sortie_temps;
            p.algorithme     = od.algorithme;
            p.param_dijkstra = od.param_dijkstra;
            p.max_nb_buckets = od.max_nb_buckets;
            p.pu             = od.pu;
            return p;
        }

        // Accès sécurisé aux dictionnaires de paramètres
        static float GetParam(Dictionary<string,float> d, string type)
        {
            if (d.TryGetValue(type, out float v)) return v;
            if (d.TryGetValue("0",  out float v0)) return v0;
            return 1f;
        }

        // ══════════════════════════════════════════════════════════════════
        //  Classes de données (inchangées sauf champs d'état retirés de link)
        // ══════════════════════════════════════════════════════════════════

        // MODIFICATION DE link :
        // Retirer les champs d'état Dijkstra (maintenant dans DijkstraState) :
        //   cout, touche, pivot, turn_pivot, service, h,
        //   tatt, tatt1, tcor, tmap, tveh, ttoll, l, ncorr,
        //   pole, poleV2, is_queue
        // Garder les champs statiques (lecture seule pendant Dijkstra) :
        //   temps, longueur, ligne, type, toll, no, nd, services,
        //   volau, boai, alij (mis à jour uniquement en phase séquentielle)

        public class link
        {
            // Champs statiques (graphe, lecture seule pendant Dijkstra)
            public float  longueur, temps, toll;
            public int    no, nd, ligne;
            public string type = "0", texte, modes, pole_static, poleV2_static;
            public bool   is_valid = true;
            public List<Service> services = new List<Service>();

            // Champs d'accumulation (mis à jour uniquement en phase séquentielle)
            public float volau, boai, alij;

            // Champs réseau non-Dijkstra
            public float v0, vsat, a, b, n, lanes;
            public int   vdf;
        }

        public class Service
        {
            public int    numero, regime;
            public float hd, hf;
            // delta, boai, alij, alit, boat, volau :
            // delta est dans DijkstraState.delta_service pendant le calcul,
            // puis boai/alij/alit/boat/volau sont accumulés en séquentiel
            public float delta, boai, alij, alit, boat, volau;
        }

        public class node
        {
            public string  i = "", texte, pole;
            public float   x, y;
            public bool    is_valid = true, is_visible, is_intersection;
            public List<int> pred = new List<int>();
            public List<int> succ = new List<int>();
        }

        public class network
        {
            public string nom;
            public List<link>  links = new List<link>(20000);
            public List<node>  nodes = new List<node>(10000);
            public float xl=1e38f, xu=-1e38f, yl=1e38f, yu=-1e38f;
            public Dictionary<string,int>    numnoeud      = new Dictionary<string,int>();
            public Dictionary<string,int>    num_calendrier= new Dictionary<string,int>();
            public List<string>              nom_calendrier= new List<string>();
            public Dictionary<string,string> noms_arcs     = new Dictionary<string,string>();
            public int max_type, nbservices;
        }

        public class etude
        {
            public string nom;
            public int    reseau_actif;
            public List<network> reseaux = new List<network>();
            public Param_affectation_horaire param_affectation_horaire
                = new Param_affectation_horaire();
        }

        public class Param_affectation_horaire
        {
            public string nom_reseau, nom_matrice, nom_sortie, nom_penalites;
            public Dictionary<string,float> coef_tmap = new Dictionary<string,float>();
            public Dictionary<string,float> cmap      = new Dictionary<string,float>();
            public Dictionary<string,float> cwait     = new Dictionary<string,float>();
            public Dictionary<string,float> cboa      = new Dictionary<string,float>();
            public Dictionary<string,float> tboa      = new Dictionary<string,float>();
            public Dictionary<string,float> tboa_max  = new Dictionary<string,float>();
            public Dictionary<string,float> cveh      = new Dictionary<string,float>();
            public Dictionary<string,float> ctoll     = new Dictionary<string,float>();
            public float  param_dijkstra, pu, tmapmax, temps_max = 120f;
            public bool   sortie_chemins, demitours = true, sortie_services,
                          sortie_turns, test_OK, sortie_noeuds = true,
                          sortie_isoles, sortie_stops;
            public int    sortie_temps, algorithme = 1, nb_jours, nb_pop;
            public float  max_nb_buckets = 10000f;
            public string texte_coef_tmap, texte_cmap, texte_cwait, texte_cboa,
                          texte_tboa, texte_tboa_max, texte_cveh, texte_toll,
                          texte_filtre_sortie = "";

            public Param_affectation_horaire Clone()
                => (Param_affectation_horaire)this.MemberwiseClone();
        }

        public class Turn
        {
            public int arci, arcj;
            public override bool Equals(object o)
                => o is Turn t && arci == t.arci && arcj == t.arcj;
            public override int GetHashCode()
                => arci.GetHashCode() ^ arcj.GetHashCode();
        }

        public class Link_num
        {
            public string i, j; public int line;
            public override bool Equals(object o)
                => o is Link_num n && i == n.i && j == n.j && line == n.line;
            public override int GetHashCode()
                => i.GetHashCode() ^ j.GetHashCode() ^ line.GetHashCode();
        }
    }
}
