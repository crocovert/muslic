﻿using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Muslic
{
    class Program
    {
        static void Main(string[] args)
        {
            if (args.Count()>3)
            {  
                string nom_reseau = args[0];
                string nom_matrice = args[1];
                string nom_sortie = args[2];
                string nom_parametres = args[3];
                string nom_penalites = null;
                if (args.Count() > 4)
                {
                    nom_penalites = args[3];
                }
                affectation_tc(nom_reseau, nom_matrice, nom_sortie, nom_parametres, nom_penalites);
            }

        }
        public static void Ecrit_parametres(Param_affectation_horaire parametres, string nom_fichier_ini)
        {

            System.IO.StreamWriter fich_ini = new System.IO.StreamWriter(nom_fichier_ini, false, System.Text.Encoding.UTF8);
            String texte = parametres.algorithme +";Algorithm"+
                "\n" + parametres.demitours + ";Prohibited U-turns"+
                "\n" + parametres.max_nb_buckets +";max buckets"+
                "\n" + parametres.nb_jours +";number of days"+
                "\n" + parametres.nom_matrice +";matrix file"+
                "\n" + parametres.nom_penalites +";turns and transfers file"+
                "\n" + parametres.nom_reseau +";network file"+
                "\n" + parametres.nom_sortie +";generic output file"+
                "\n" + parametres.param_dijkstra +";algorithm paramter+"+
                "\n" + parametres.pu +";algorithm power"+
                "\n" + parametres.sortie_chemins +";output paths"+
                "\n" + parametres.sortie_services +";output services"+
                "\n" + parametres.sortie_temps +";output travael times"+
                "\n" + parametres.sortie_turns +";output turns and transfers"+
                "\n" + parametres.texte_cboa +";boarding weight"+
                "\n" + parametres.texte_cmap +";individual mode weight"+
                "\n" + parametres.texte_coef_tmap +";indivudal travel time factor"+
                "\n" + parametres.texte_cveh +";in-vehicle time weight"+
                "\n" + parametres.texte_cwait +";wait tim weight"+
                "\n" + parametres.texte_tboa +";min transfer time"+

                "\n" + parametres.texte_tboa_max +";max transfer time"+
                "\n" + parametres.tmapmax +";max individual travel time "+
                "\n" + parametres.texte_toll +";toll weight"+
                "\n" + parametres.texte_filtre_sortie +";output filter types"+
                "\n" + parametres.temps_max +";max travel cost"+
                "\n" + parametres.sortie_noeuds +";output nodes"+
                "\n" + parametres.sortie_isoles+";output isolated links";

            fich_ini.WriteLine(texte);
            fich_ini.Close();






        }



        public static Param_affectation_horaire lit_parametres(string nom_parametres)
        {
           
            Param_affectation_horaire aff_hor = new Param_affectation_horaire();
            if (System.IO.File.Exists(nom_parametres) == true)
            {
                System.IO.StreamReader fich_ini = new System.IO.StreamReader(nom_parametres);

                aff_hor.algorithme = int.Parse(fich_ini.ReadLine().Split(';')[0]);
//                Console.WriteLine(aff_hor.algorithme);
                aff_hor.demitours = bool.Parse(fich_ini.ReadLine().Split(';')[0]);
                //Console.WriteLine(aff_hor.demitours);
                aff_hor.max_nb_buckets = int.Parse(fich_ini.ReadLine().Split(';')[0]);
                //Console.WriteLine(aff_hor.max_nb_buckets);
                aff_hor.nb_jours = int.Parse(fich_ini.ReadLine().Split(';')[0]);
                //Console.WriteLine(aff_hor.nb_jours);
                aff_hor.nom_matrice = fich_ini.ReadLine().Split(';')[0];
                //Console.WriteLine(aff_hor.nom_matrice);
                aff_hor.nom_penalites = fich_ini.ReadLine().Split(';')[0];
                //Console.WriteLine(aff_hor.nom_penalites);
                aff_hor.nom_reseau = fich_ini.ReadLine().Split(';')[0];
                //Console.WriteLine(aff_hor.nom_reseau);
                aff_hor.nom_sortie = fich_ini.ReadLine().Split(';')[0];
                //Console.WriteLine(aff_hor.nom_sortie);
                aff_hor.param_dijkstra = int.Parse(fich_ini.ReadLine().Split(';')[0]);
                //Console.WriteLine(aff_hor.param_dijkstra);
                aff_hor.pu = float.Parse(fich_ini.ReadLine().Split(';')[0]);
                //Console.WriteLine(aff_hor.pu);
                aff_hor.sortie_chemins = bool.Parse(fich_ini.ReadLine().Split(';')[0]);
                //Console.WriteLine(aff_hor.sortie_chemins);
                aff_hor.sortie_services = bool.Parse(fich_ini.ReadLine().Split(';')[0]);
                //Console.WriteLine(aff_hor.sortie_services);
                aff_hor.sortie_temps = int.Parse(fich_ini.ReadLine().Split(';')[0]);
                //Console.WriteLine(aff_hor.sortie_temps);
                aff_hor.sortie_turns = bool.Parse(fich_ini.ReadLine().Split(';')[0]);
                //Console.WriteLine(aff_hor.sortie_turns);
                aff_hor.texte_cboa = fich_ini.ReadLine().Split(';')[0];
                //Console.WriteLine(aff_hor.texte_cboa);
                aff_hor.texte_cmap = fich_ini.ReadLine().Split(';')[0];
                //Console.WriteLine(aff_hor.texte_cmap);
                aff_hor.texte_coef_tmap = fich_ini.ReadLine().Split(';')[0];
                //Console.WriteLine(aff_hor.texte_coef_tmap);
                aff_hor.texte_cveh = fich_ini.ReadLine().Split(';')[0];
                //Console.WriteLine(aff_hor.texte_cveh);
                aff_hor.texte_cwait = fich_ini.ReadLine().Split(';')[0];
                //Console.WriteLine(aff_hor.texte_cwait);
                aff_hor.texte_tboa = fich_ini.ReadLine().Split(';')[0];
                //Console.WriteLine(aff_hor.texte_tboa);
                aff_hor.texte_tboa_max = fich_ini.ReadLine().Split(';')[0];
                //Console.WriteLine(aff_hor.texte_tboa_max);

                if (fich_ini.EndOfStream == false)
                {
                    if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                    {
                        aff_hor.tmapmax = float.Parse(fich_ini.ReadLine().Replace(",", ".").Split(';')[0]);
                    }
                    else
                    {
                        aff_hor.tmapmax = float.Parse(fich_ini.ReadLine().Replace(".", ",").Split(';')[0]);
                    }

                  //  Console.WriteLine(aff_hor.tmapmax);
                }
                if (fich_ini.EndOfStream == false)
                {
                    aff_hor.texte_toll = fich_ini.ReadLine().Split(';')[0];
                    //Console.WriteLine(aff_hor.texte_toll);
                }
            
                if (fich_ini.EndOfStream == false)
                {
                    aff_hor.texte_filtre_sortie = fich_ini.ReadLine().Split(';')[0];
                   //Console.WriteLine(aff_hor.texte_filtre_sortie);
            }
        

                if (fich_ini.EndOfStream == false)
                {
                    if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                    {
                        aff_hor.temps_max = float.Parse(fich_ini.ReadLine().Replace(",",".").Split(';')[0]);
                    }
                    else
                    {
                        aff_hor.temps_max = float.Parse(fich_ini.ReadLine().Replace(".", ",").Split(';')[0]);
                    }
                    //Console.WriteLine(aff_hor.temps_max);
                }
                if (fich_ini.EndOfStream == false)
                {
                    aff_hor.sortie_noeuds = bool.Parse(fich_ini.ReadLine().Split(';')[0]);
                    //Console.WriteLine(aff_hor.sortie_noeuds);
                }
                if (fich_ini.EndOfStream == false)
                {
                    aff_hor.sortie_isoles = bool.Parse(fich_ini.ReadLine().Split(';')[0]);
                    //Console.WriteLine(aff_hor.sortie_isoles);
                }
                fich_ini.Close();
            }
            aff_hor.test_OK = true;
            return aff_hor;
        }

        public static void affectation_tc(string nom_reseau, string nom_matrice, string nom_sortie, string nom_parametres, string nom_penalites)
        {
            int i, j;

            HashSet<String> types = new HashSet<string>();
            Dictionary<Turn, float> turns = new Dictionary<Turn, float>();
            Dictionary<Turn, float> transfers = new Dictionary<Turn, float>();
            Dictionary<Link_num, int> link_id = new Dictionary<Link_num, int>();
            etude projet = new etude();
            Param_affectation_horaire aff_hor = lit_parametres(nom_parametres);
            //string nom_reseau = aff_hor.nom_reseau;
            //string nom_matrice = aff_hor.nom_matrice;
            //string nom_penalites = aff_hor.nom_penalites;
            //Console.WriteLine(nom_sortie);
            projet.param_affectation_horaire = aff_hor;
            aff_hor.nom_sortie = nom_sortie;
            aff_hor.nom_reseau = nom_reseau;
            aff_hor.nom_matrice = nom_matrice;
            aff_hor.nom_penalites = nom_penalites;
            if (System.IO.File.Exists(nom_parametres)==true)
            {
                if (System.IO.File.Exists(nom_reseau) == true && System.IO.File.Exists(nom_matrice) == true && projet.param_affectation_horaire.test_OK == true)
                {

                    string[] param = { ";" };
                    if (projet.reseaux.Count > 0)
                    {
                        projet.reseaux.RemoveAt(projet.reseaux.Count - 1);
                    }
                    projet.reseaux.Add(new network());
                    int num_res;


                    string chaine;
                    string[] ch;

                    projet.reseau_actif = projet.reseaux.Count - 1;
                    num_res = projet.reseaux.Count - 1;
                    //openFileDialog1.ShowDialog();

                    string carte = "t links";

                    int avancement=0;
                    int ctop = Console.CursorTop;
                    int cleft = Console.CursorLeft;
                    Console.SetCursorPosition(cleft, ctop);
                    Console.Write("Network import:" + avancement + "%");
                    //            System.Globalization.NumberFormatInfo.CurrentInfo.CurrencyDecimalSeparator = ".";
                    System.IO.FileStream flux;

                    flux = new System.IO.FileStream(nom_reseau, System.IO.FileMode.Open,FileAccess.Read,System.IO.FileShare.Read);
                    System.IO.StreamReader fichier_reseau = new System.IO.StreamReader(flux, Encoding.UTF8);
                    //   projet.reseaux[num_res].matrices.Add(new matrix());
                    System.IO.StreamWriter fich_log = new System.IO.StreamWriter(aff_hor.nom_sortie + "_log.txt", false, System.Text.Encoding.UTF8);
                    fich_log.WriteLine("Version: Muslic " + System.Reflection.Assembly.GetExecutingAssembly().GetName().Version.ToString());
                    fich_log.WriteLine("Process start time: " + System.DateTime.Now.ToString("dddd dd MMMM yyyy HH:mm:ss.fff"));
                    fich_log.WriteLine("Default parameters:");
                    fich_log.WriteLine("Minimum transfer time:" + aff_hor.texte_tboa);
                    fich_log.WriteLine("Maximum transfer time:" + aff_hor.texte_tboa_max);
                    fich_log.WriteLine("Transfer weight:" + aff_hor.texte_cboa);
                    fich_log.WriteLine("Wait weight:" + aff_hor.texte_cwait);
                    fich_log.WriteLine("Time based links weight:" + aff_hor.texte_cveh);
                    fich_log.WriteLine("Individual links weight:" + aff_hor.texte_cmap);
                    fich_log.WriteLine("Individual travel time factor:" + aff_hor.texte_coef_tmap);
                    fich_log.WriteLine("Generalized travel time maximum:" + aff_hor.temps_max);
                    fich_log.WriteLine("Individual travel time maximum:" + aff_hor.tmapmax.ToString());
                    fich_log.WriteLine("Toll weight:" + aff_hor.texte_toll.ToString());
                    fich_log.WriteLine("Number of days:" + aff_hor.nb_jours);
                    fich_log.WriteLine("Prohibited U-turns:" + aff_hor.demitours);

                    fich_log.WriteLine("Algorithm:" + aff_hor.algorithme);
                    fich_log.WriteLine("Algorithm number of buckets:" + aff_hor.max_nb_buckets);
                    fich_log.WriteLine("Algorithm scale parameter:" + aff_hor.param_dijkstra);
                    fich_log.WriteLine("Algorithm power parameter:" + aff_hor.pu);

                    fich_log.WriteLine("Output paths:" + aff_hor.sortie_chemins);
                    fich_log.WriteLine("Output times:" + aff_hor.sortie_temps);
                    fich_log.WriteLine("Output filenames:" + aff_hor.nom_sortie);
                    fich_log.WriteLine("Link type filter:" + aff_hor.texte_filtre_sortie.ToString());
                    fich_log.WriteLine("Output nodes:" + aff_hor.sortie_noeuds.ToString());
                    fich_log.WriteLine("Output isolated nodes:" + aff_hor.sortie_isoles.ToString());

                    

                    projet.reseaux[projet.reseau_actif].nom = System.IO.Path.GetFileNameWithoutExtension(nom_reseau);
                lec:
                    while (fichier_reseau.EndOfStream == false)
                    {
                    lecture:

                        chaine = fichier_reseau.ReadLine();

                        if (avancement< (int)((100 * flux.Position) / flux.Length) - 4)
                        {
                            Console.SetCursorPosition(cleft, ctop);
                            Console.Write( "Network import:" + ((100 * flux.Position) / flux.Length).ToString() + "%");
                            avancement = (int)((100 * flux.Position) / flux.Length);
                            
                        }

                        if (chaine.Trim().Length == 0) goto lec;
                        if (chaine.Substring(0, 7) == "t nodes")
                        {
                            carte = "t nodes";
                            goto lecture;
                        }
                        else if (chaine.Substring(0, 7) == "t links")
                        {
                            carte = "t links";
                            goto lecture;
                        }



                        ch = chaine.Split(param, System.StringSplitOptions.None);
                        //MessageBox.Show(carte + " " + ch[0]);
                        //if ((Convert.ToSingle(ch[4]) > projet.param_affectation_horaire.deb_per && Convert.ToSingle(ch[4]) < projet.param_affectation_horaire.fin_per) || Convert.ToSingle(ch[4])<0)
                        if (carte == "t nodes")
                        {
                            string ni = ch[0].Trim();
                            if (projet.reseaux[projet.reseau_actif].numnoeud.ContainsKey(ni) == false)
                            {
                                projet.reseaux[projet.reseau_actif].numnoeud.Add(ni, projet.reseaux[projet.reseau_actif].nodes.Count);

                                float xi, yi;
                                if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                                {
                                    xi = float.Parse(ch[1].Replace(',', '.'));
                                    yi = float.Parse(ch[2].Replace(',', '.'));
                                }
                                else
                                {
                                    xi = float.Parse(ch[1].Replace('.', ','));
                                    yi = float.Parse(ch[2].Replace('.', ','));
                                }
                                node noeud = new node();
                                node nul = new node();
                                noeud.i = ni;
                                noeud.x = xi;
                                noeud.y = yi;
                                noeud.is_visible = true;
                                if (xi > projet.reseaux[num_res].xu)
                                {
                                    projet.reseaux[num_res].xu = xi;
                                }
                                if (xi < projet.reseaux[num_res].xl)
                                {
                                    projet.reseaux[num_res].xl = xi;
                                }
                                if (yi > projet.reseaux[num_res].yu)
                                {

                                    projet.reseaux[num_res].yu = yi;

                                }
                                if (yi < projet.reseaux[num_res].yl)
                                {
                                    projet.reseaux[num_res].yl = yi;
                                }


                                if (ch.Length > 3)
                                {
                                    noeud.texte = ch[3];
                                }


                                projet.reseaux[projet.reseau_actif].nodes.Add(noeud);
                            }

                        }
                        else if (carte == "t links")
                        {
                            node nul = new node();
                            node nodei = new node();
                            node nodej = new node();
                            Link_num num_link = new Link_num();

                            string ni = ch[0].Trim();
                            int line;
                            nodei.i = ni;
                            /*while (projet.reseaux[projet.reseau_actif].nodes.Count < ni + 1)
                            {
                                projet.reseaux[projet.reseau_actif].nodes.Add(nul);
                            }
                            //projet.reseaux[projet.reseau_actif].numnoeud.Add(ni, projet.reseaux[projet.reseau_actif].nodes.Count);*/
                            int value;
                            if (projet.reseaux[projet.reseau_actif].numnoeud.TryGetValue(ni, out value) == false)
                            {
                                projet.reseaux[projet.reseau_actif].numnoeud.Add(ni, projet.reseaux[projet.reseau_actif].nodes.Count);
                                projet.reseaux[projet.reseau_actif].nodes.Add(nodei);
                            }
                            /*if (projet.reseaux[projet.reseau_actif].nodes[ni].i == 0)
                            {
                                projet.reseaux[projet.reseau_actif].nodes[ni] = nodei;
                            }*/

                            string nj = ch[1].Trim();

                            nodej.i = nj;
                            /*while (projet.reseaux[projet.reseau_actif].nodes.Count < nj + 1)
                            {
                                projet.reseaux[projet.reseau_actif].nodes.Add(nul);
                            }
                            if (projet.reseaux[projet.reseau_actif].nodes[nj].i == 0)
                            {
                                projet.reseaux[projet.reseau_actif].nodes[nj] = nodej;
                            }*/
                            //  MessageBox.Show(projet.reseaux[projet.reseau_actif].numnoeud.TryGetValue(nj, out value).ToString()+" "+nj.ToString()+" "+value.ToString());
                            if (projet.reseaux[projet.reseau_actif].numnoeud.TryGetValue(nj, out value) == false)
                            {
                                projet.reseaux[projet.reseau_actif].numnoeud.Add(nj, projet.reseaux[projet.reseau_actif].nodes.Count);
                                projet.reseaux[projet.reseau_actif].nodes.Add(nodej);
                            }


                            link lien = new link();
                            lien.no = projet.reseaux[projet.reseau_actif].numnoeud[ni];
                            lien.nd = projet.reseaux[projet.reseau_actif].numnoeud[nj];
                            line = Convert.ToInt32(ch[4]);
                            num_link.i = ni;
                            num_link.j = nj;
                            num_link.line = line;




                            Service num_service = new Service();
                            num_service.numero = -1;
                            if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                            {
                                lien.temps = float.Parse(ch[2].Replace(',', '.'));
                                lien.longueur = float.Parse(ch[3].Replace(',', '.'));
                                num_service.numero = int.Parse(ch[5].Replace(',', '.'));
                                num_service.hd = float.Parse(ch[6].Replace(',', '.'));
                                num_service.hf = float.Parse(ch[7].Replace(',', '.'));
                            }
                            else
                            {
                                lien.temps = float.Parse(ch[2].Replace('.', ','));
                                lien.longueur = float.Parse(ch[3].Replace('.', ','));
                                num_service.numero = int.Parse(ch[5].Replace('.', ','));
                                num_service.hd = float.Parse(ch[6].Replace('.', ','));
                                num_service.hf = float.Parse(ch[7].Replace('.', ','));
                            }
                            if (num_service.hd < 100f && num_service.numero >= 0)
                            {
                                // num_service.hd += 1440f;
                            }
                            if (num_service.hf < 100f && num_service.numero >= 0)
                            {
                                //num_service.hf += 1440f;
                            }
                            if (num_service.hf < num_service.hd)
                            {
                                num_service.hf += 1440f;
                            }

                            if (projet.reseaux[projet.reseau_actif].num_calendrier.TryGetValue(ch[8].ToString().Trim(), out value) == false)
                            {
                                projet.reseaux[projet.reseau_actif].num_calendrier.Add(ch[8].ToString().Trim(), projet.reseaux[projet.reseau_actif].nom_calendrier.Count);
                                projet.reseaux[projet.reseau_actif].nom_calendrier.Add(ch[8].ToString().Trim());

                            }

                            num_service.regime = projet.reseaux[projet.reseau_actif].num_calendrier[ch[8].ToString().Trim()];

                            int nb = projet.reseaux[projet.reseau_actif].links.Count;




                            /*dictionnaire lien*/
                            if (link_id.ContainsKey(num_link) == true && num_service.numero > 0)
                            {
                                projet.reseaux[projet.reseau_actif].links[link_id[num_link]].services.Add(num_service);
                                projet.reseaux[projet.reseau_actif].nbservices += 1;

                            }
                            else
                            {
                                lien.ligne = line;
                                if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                                {
                                    lien.temps = float.Parse(ch[2].Replace(',', '.'));
                                    lien.longueur = float.Parse(ch[3].Replace(',', '.'));
                                }
                                else
                                {
                                    lien.temps = float.Parse(ch[2].Replace('.', ','));
                                    lien.longueur = float.Parse(ch[3].Replace('.', ','));
                                }

                                if (num_service.numero > 0)
                                {
                                    lien.services.Add(num_service);
                                    projet.reseaux[projet.reseau_actif].nbservices += 1;
                                }
                                if (ch.Length > 9)
                                {
                                    if (ch[9].Length > 0)
                                    {
                                        lien.texte = ch[9];
                                    }
                                    else
                                    {
                                        lien.texte = " ";
                                    }
                                }
                                if (ch.Length > 10)
                                {

                                    lien.type = ch[10].Trim().ToString();
                                    if (types.Contains(lien.type) == false)
                                    {
                                        types.Add(lien.type);
                                    }

                                }
                                else
                                {

                                    lien.type = "0";
                                }

                                if (ch.Length > 11)
                                {
                                    if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                                    {
                                        lien.toll = float.Parse(ch[11].Replace(',', '.'));
                                    }
                                    else
                                    {
                                        lien.toll = float.Parse(ch[11].Replace('.', ','));
                                    }
                                }



                                projet.reseaux[projet.reseau_actif].links.Add(lien);
                                link_id[num_link] = projet.reseaux[projet.reseau_actif].links.Count - 1;

                            }

                            /*                        if (nb > 0 )                        
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].links[nb - 1].no == projet.reseaux[projet.reseau_actif].numnoeud[ni] && projet.reseaux[projet.reseau_actif].links[nb - 1].nd == projet.reseaux[projet.reseau_actif].numnoeud[nj] && projet.reseaux[projet.reseau_actif].links[nb - 1].ligne == line && num_service.numero > 0)
                                                        {

                                                            projet.reseaux[projet.reseau_actif].links[nb - 1].services.Add(num_service);
                                                            projet.reseaux[projet.reseau_actif].nbservices += 1;

                                                        }
                                                        else
                                                        {
                                                            lien.ligne = line;
                                                            if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                                                            {
                                                                lien.temps = float.Parse(ch[2].Replace(',', '.'));
                                                                lien.longueur = float.Parse(ch[3].Replace(',', '.'));
                                                            }
                                                            else
                                                            {
                                                                lien.temps = float.Parse(ch[2].Replace('.', ','));
                                                                lien.longueur = float.Parse(ch[3].Replace('.', ','));
                                                            }

                                                            if (num_service.numero >0)
                                                            {
                                                                lien.services.Add(num_service);
                                                                projet.reseaux[projet.reseau_actif].nbservices += 1;
                                                            }
                                                            if (ch.Length > 9)
                                                            {
                                                                lien.texte = ch[9];
                                                            }
                                                            if (ch.Length > 10)
                                                            {
                                                                lien.type = int.Parse(ch[10]);
                                                                if (lien.type > projet.reseaux[projet.reseau_actif].max_type)
                                                                {
                                                                    projet.reseaux[projet.reseau_actif].max_type = lien.type;

                                                                }
                                                            }

                                                            if (ch.Length > 11)
                                                            {
                                                                if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                                                                {
                                                                    lien.toll = float.Parse(ch[11].Replace(',', '.'));
                                                                }
                                                                else
                                                                {
                                                                    lien.toll = float.Parse(ch[11].Replace('.', ','));
                                                                }
                                                            }



                                                            projet.reseaux[projet.reseau_actif].links.Add(lien);
                                                        }

                                                    }
                                                        else
                                                    {
                                                            lien.ligne = line;
                                                            if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                                                            {
                                                                lien.temps = float.Parse(ch[2].Replace(',','.'));
                                                                lien.longueur = float.Parse(ch[3].Replace(',', '.'));
                                                            }
                                                            else
                                                            {
                                                                lien.temps = float.Parse(ch[2].Replace('.', ','));
                                                                lien.longueur = float.Parse(ch[3].Replace('.', ','));


                                                            }
                                                            if (num_service.numero > 0)
                                                            {
                                                                lien.services.Add(num_service);
                                                                projet.reseaux[projet.reseau_actif].nbservices += 1;
                                                            }
                                                            if (ch.Length > 9)
                                                            {
                                                                lien.texte = ch[9];
                                                            }

                                                            if (ch.Length > 10)
                                                            {
                                                                lien.type = int.Parse(ch[10]);
                                                                if (lien.type > projet.reseaux[projet.reseau_actif].max_type)
                                                                {
                                                                    projet.reseaux[projet.reseau_actif].max_type = lien.type;

                                                                }
                                                            }
                                                            if (ch.Length > 11)
                                                            {
                                                                if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                                                                {
                                                                    lien.toll = float.Parse(ch[11].Replace(',', '.'));
                                                                }
                                                                else
                                                                {
                                                                    lien.toll = float.Parse(ch[11].Replace('.', ','));
                                                                }
                                                            }



                                                            projet.reseaux[projet.reseau_actif].links.Add(lien);
                                                       }


                              */

                        }
                    }
                    fichier_reseau.Close();

                    /*    for (int k = 0; k <= projet.reseaux[projet.reseau_actif].max_type; k++)
                        {
                            projet.param_affectation_horaire.cveh.Add(1f);
                            projet.param_affectation_horaire.coef_tmap.Add(1f);
                            projet.param_affectation_horaire.cmap.Add(1f);
                            projet.param_affectation_horaire.cboa.Add(1f);
                            projet.param_affectation_horaire.tboa.Add(1f);
                            projet.param_affectation_horaire.cwait.Add(1f);
                            projet.param_affectation_horaire.tboa_max.Add(1f);
                            projet.param_affectation_horaire.ctoll.Add(1f);

                        }*/

                    fich_log.WriteLine("Network:" + nom_reseau);
                    fich_log.WriteLine("Nodes:" + projet.reseaux[projet.reseau_actif].nodes.Count);
                    fich_log.WriteLine("Links:" + projet.reseaux[projet.reseau_actif].links.Count);

                    //construction du graphe
                    // table des prédécesseurs et successeurs de noeuds
                    avancement = 0;
                    Console.WriteLine();
                    ctop = Console.CursorTop;
                    cleft = Console.CursorLeft;

                    for (i = 0; i < projet.reseaux[projet.reseau_actif].links.Count; i++)
                    {
                        //virage.distance = 0;
                        //virage.cout = 0;

                        projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[i].nd].pred.Add(i);
                        projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[i].no].succ.Add(i);
                        //                    Console.SetCursorPosition(1, Console.CursorTop-1);

                        if (avancement < (int)((100 * (i+1)) / projet.reseaux[projet.reseau_actif].links.Count) - 4)
                        {
                            avancement = (int)((100 * (i+1)) / projet.reseaux[projet.reseau_actif].links.Count);
                            Console.SetCursorPosition(cleft, ctop);
                            Console.Write("Network topology generation:" + ((100 * (i+1)) / projet.reseaux[projet.reseau_actif].links.Count).ToString() + "%");

                        }

                    }

                    avancement = 0;

                    // table des prédécesseurs et successeurs de tronçons
                    //Console.WriteLine("création de la topologie des noeuds terminée");
                    
                    Console.WriteLine();
                    ctop = Console.CursorTop;
                    cleft = Console.CursorLeft;

                    /*for (j = 0; j < projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[i].no].pred.Count; j++)
                    {
                        turn virage = new turn();
                        int predecesseur = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[i].no].pred[j];

                        {
                            virage.numero = predecesseur;
                            virage.temps = 0;
                            projet.reseaux[projet.reseau_actif].links[i].arci.Add(virage);
                            if (projet.reseaux[projet.reseau_actif].links[i].nd == projet.reseaux[projet.reseau_actif].links[predecesseur].no && projet.param_affectation_horaire.demitours == true)
                            {
                                projet.reseaux[projet.reseau_actif].links[i].arci[j].temps = -1;
                                projet.reseaux[projet.reseau_actif].links[i].arci[j].is_valid = true;
                            }
                        }

                    
                    }*/
                    /* for (j = 0; j < projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[i].nd].succ.Count; j++)
                     {
                         turn virage = new turn();
                         int successeur = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[i].nd].succ[j];
                         {
                             virage.numero = successeur;
                             virage.temps = 0;
                             projet.reseaux[projet.reseau_actif].links[i].arcj.Add(virage);
                             projet.reseaux[projet.reseau_actif].nbturns += 1;
                             if (projet.reseaux[projet.reseau_actif].links[i].no == projet.reseaux[projet.reseau_actif].links[successeur].nd && projet.param_affectation_horaire.demitours == true)
                             {
                                 projet.reseaux[projet.reseau_actif].links[i].arcj[j].temps = -1;
                                 projet.reseaux[projet.reseau_actif].links[i].arcj[j].is_valid = true;

                             }
                         }

                     }*/



                    //fich_log.WriteLine("Virages et correspondances:" + projet.reseaux[projet.reseau_actif].nbturns);
                    fich_log.WriteLine("Time based services:" + projet.reseaux[projet.reseau_actif].nbservices);

                    /*************************Import des pénalités et temps de correspondances************************/
                    /*************************Import des pénalités et temps de correspondances************************/
                    /*************************Import des pénalités et temps de correspondances************************/
                    /*************************Import des pénalités et temps de correspondances************************/
                    /*************************Import des pénalités et temps de correspondances************************/
                    /*************************Import des pénalités et temps de correspondances************************/
                    /*************************Import des pénalités et temps de correspondances************************/

                    if (System.IO.File.Exists(nom_penalites) == true && System.IO.File.Exists(nom_reseau) == true && System.IO.File.Exists(nom_matrice) == true && nom_reseau != null && nom_matrice != null)
                    {
                        fich_log.WriteLine("Penalties and transfers:" + nom_penalites);
                        string[] penal;
                        int ni, nj, nk;
                        int linei, linej, ntri, ntrj;
                        float tps_mvt;
                        flux.Close();
                        flux = new System.IO.FileStream(nom_penalites, System.IO.FileMode.Open,FileAccess.Read,FileShare.Read);
                        System.IO.StreamReader fichier_penalites = new System.IO.StreamReader(flux, System.Text.Encoding.UTF8);
                        while (fichier_penalites.EndOfStream == false)
                        {
                            if (avancement < (int)((100 * flux.Position) / flux.Length) - 4)
                            {
                                Console.SetCursorPosition(cleft, ctop);
                                Console.Write("Penalties and transfers import:" + ((100 * flux.Position) / flux.Length).ToString() + "%");
                                avancement = (int)((100 * flux.Position) / flux.Length);
                                
                            }


                            chaine = fichier_penalites.ReadLine();
                            ntri = -1; ntrj = -1;
                            penal = chaine.Split(param, System.StringSplitOptions.RemoveEmptyEntries);
                            nj = projet.reseaux[projet.reseau_actif].numnoeud[penal[0].Trim()];
                            ni = projet.reseaux[projet.reseau_actif].numnoeud[penal[1].Trim()];
                            linei = int.Parse(penal[2]);
                            nk = projet.reseaux[projet.reseau_actif].numnoeud[penal[3].Trim()];
                            linej = int.Parse(penal[4]);
                            if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                            {
                                tps_mvt = float.Parse(penal[5].Replace(',', '.'));
                            }
                            else
                            {
                                tps_mvt = float.Parse(penal[5].Replace('.', ','));
                            }
                            for (i = 0; i < projet.reseaux[projet.reseau_actif].nodes[nj].pred.Count; i++)
                            {
                                if (projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].nodes[nj].pred[i]].no == ni && projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].nodes[nj].pred[i]].ligne == linei)
                                {
                                    ntri = projet.reseaux[projet.reseau_actif].nodes[nj].pred[i];
                                }
                            }
                            for (i = 0; i < projet.reseaux[projet.reseau_actif].nodes[nj].succ.Count; i++)
                            {
                                if (projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].nodes[nj].succ[i]].nd == nk && projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].nodes[nj].succ[i]].ligne == linej)
                                {
                                    ntrj = projet.reseaux[projet.reseau_actif].nodes[nj].succ[i];
                                }
                            }
                            if (ntrj >= 0 && ntri >= 0)
                            {
                                Turn virage = new Turn();
                                virage.arci = ntri;
                                virage.arcj = ntrj;
                                float value;
                                if (turns.TryGetValue(virage, out value) == false)
                                {
                                    turns.Add(virage, tps_mvt);
                                }
                                projet.reseaux[projet.reseau_actif].nodes[nj].is_intersection = true;
                                /*  for (i = 0; i < projet.reseaux[projet.reseau_actif].links[ntrj].arci.Count; i++)
                                  {
                                      if (projet.reseaux[projet.reseau_actif].links[ntrj].arci[i].numero == ntri)
                                      {
                                          projet.reseaux[projet.reseau_actif].links[ntrj].arci[i].temps = tps_mvt;
                                          projet.reseaux[projet.reseau_actif].links[ntrj].arci[i].is_valid = true;

                                      }
                                  }
                                  for (i = 0; i < projet.reseaux[projet.reseau_actif].links[ntri].arcj.Count; i++)
                                  {
                                      if (projet.reseaux[projet.reseau_actif].links[ntri].arcj[i].numero == ntrj)
                                      {
                                          projet.reseaux[projet.reseau_actif].links[ntri].arcj[i].temps = tps_mvt;
                                          projet.reseaux[projet.reseau_actif].links[ntri].arcj[i].is_valid = true;

                                      }
                                  }*/
                            }

                        }


                    }
                    Console.SetCursorPosition(cleft, ctop);
                    Console.Write("Penalties and transfers import:" + (100 ).ToString() + "%");


                    ////écrire réseau en XML////

                    /*network Export = projet.reseaux[projet.reseau_actif];
                    System.Xml.Serialization.XmlSerializer writer =
                    new System.Xml.Serialization.XmlSerializer(Export.GetType());
                    System.IO.StreamWriter file = new System.IO.StreamWriter( projet.param_affectation_horaire.nom_sortie+ ".xml");

                    writer.Serialize(file, Export);
                    file.Close();*/



                    //affectation tc à horaires algorithme
                    // graph growth aglorithm with buckets
                    // graph growth aglorithm with buckets
                    // graph growth aglorithm with buckets
                    // graph growth aglorithm with buckets
                    // graph growth aglorithm with buckets
                    // graph growth aglorithm with buckets
                    // graph growth aglorithm with buckets
                    // graph growth aglorithm with buckets
                    if (projet.param_affectation_horaire.algorithme <= 1)
                    {


                        System.IO.StreamWriter fich_sortie = new System.IO.StreamWriter(projet.param_affectation_horaire.nom_sortie + "_temps.txt", false, Encoding.UTF8);
                        System.IO.StreamWriter fich_sortie2 = new System.IO.StreamWriter(projet.param_affectation_horaire.nom_sortie + "_chemins.txt", false, Encoding.UTF8);
                        System.IO.StreamWriter fich_result = new System.IO.StreamWriter(projet.param_affectation_horaire.nom_sortie + "_aff.txt", false, Encoding.UTF8);
                        System.IO.StreamWriter fich_od = new System.IO.StreamWriter(projet.param_affectation_horaire.nom_sortie + "_od.txt", false, Encoding.UTF8);
                        System.IO.StreamWriter fich_noeuds = new System.IO.StreamWriter(projet.param_affectation_horaire.nom_sortie + "_noeuds.txt", false, Encoding.UTF8);
                        System.IO.StreamWriter fich_detour = new System.IO.StreamWriter(projet.param_affectation_horaire.nom_sortie + "_detour.txt", false, Encoding.UTF8);
                        System.IO.StreamWriter fich_isoles = new System.IO.StreamWriter(projet.param_affectation_horaire.nom_sortie + "_isoles.txt", false, Encoding.UTF8);
                        Ecrit_parametres(projet.param_affectation_horaire,projet.param_affectation_horaire.nom_sortie + "_param.txt");
                        fich_sortie.WriteLine("id;o;ij;ligne;numtrc;jour;heureo;heured;temps;tveh;tmap;tatt;tcorr;ncorr;tatt1;cout;longueur;pole;volau;precedent;type;toll;ti");
                        fich_sortie2.WriteLine("id;o;d;jour;heure;i;j;ligne;service;temps;heureo;tveh;tmap;tatt;tcorr;ncorr;tatt1;cout;longueur;pole;volau;boai;alij;texte;type;toll");
                        fich_result.WriteLine("i;j;ligne;volau;boai;alij;texte;type;toll");
                        fich_od.WriteLine("id;o;d;jour;heureo;heured;temps;tveh;tmap;tatt;tcorr;ncorr;tatt1;cout;longueur;pole;volau;texte;nbpop;toll");
                        fich_noeuds.WriteLine("id;o;d;jour;numero;heureo;heured;temps;tveh;tmap;tatt;tcorr;ncorr;tatt1;cout;longueur;pole;toll");



                        // Console.WriteLine("création de la topologie des tronçons terminée");
                        //plus courts chemins
                        Queue<int> touches = new Queue<int>();
                        Queue<int> calcules = new Queue<int>();
                        List<List<int>> gga_nq = new List<List<int>>();

                        avancement = 0;
                        Console.WriteLine();
                        ctop = Console.CursorTop;
                        cleft = Console.CursorLeft;


                        //initilisation
                        for (i = 0; i < projet.reseaux[projet.reseau_actif].links.Count; i++)
                        {
                            projet.reseaux[projet.reseau_actif].links[i].l = 0;
                            projet.reseaux[projet.reseau_actif].links[i].volau = 0;
                            projet.reseaux[projet.reseau_actif].links[i].touche = 0;
                            projet.reseaux[projet.reseau_actif].links[i].cout = 0;
                            projet.reseaux[projet.reseau_actif].links[i].pivot = -1;
                            projet.reseaux[projet.reseau_actif].links[i].is_queue = false;
                            //                projet.reseaux[projet.reseau_actif].links[i].temps = projet.reseaux[projet.reseau_actif].links[i].fd(projet.reseaux[projet.reseau_actif].links[i].volau, projet.reseaux[projet.reseau_actif].links[i].longueur, 0f, projet.reseaux[projet.reseau_actif].links[i].lanes * 1000, projet.reseaux[projet.reseau_actif].links[i].v0, projet.reseaux[projet.reseau_actif].links[i].a, projet.reseaux[projet.reseau_actif].links[i].b, projet.reseaux[projet.reseau_actif].links[i].n);

                        }


                        string p, q, p1 = "", q1 = "", libod = "";
                        int sens = 1, sens1 = 0, jour1 = 0, numod = 0;
                        float horaire1 = 0;
                        flux.Close();

                        flux = new System.IO.FileStream(nom_matrice, System.IO.FileMode.Open,FileAccess.Read,FileShare.Read);
                        System.IO.StreamReader fichier_matrice = new System.IO.StreamReader(flux, System.Text.Encoding.UTF8);
                        avancement = 0;
                        fich_log.WriteLine("Matrix:" + nom_matrice);
                        DateTime t1 = DateTime.Now;
                        fich_log.WriteLine("Computation start time: " + t1.ToString("dddd dd MMMM yyyy HH:mm:ss.fff"));
                        fich_log.Flush();
                    lec1:
                        while (fichier_matrice.EndOfStream == false)
                        {
                        lecture:
                            projet.param_affectation_horaire.nb_pop = 0;
                            chaine = fichier_matrice.ReadLine();
                            if (avancement < (int)((100 * flux.Position) / flux.Length))
                            {
                                Console.SetCursorPosition(cleft, ctop);
                                Console.Write( "Shortest paths computing...:" + ((100 * flux.Position) / flux.Length).ToString() + "%");
                                avancement = (int)((100 * flux.Position) / flux.Length);
                                
                            }
                            if (chaine.Trim().Length == 0) goto lec1;
                            if (chaine == "")
                            {
                                goto lecture;
                            }
                            numod++;
                            ch = chaine.Split(param, StringSplitOptions.RemoveEmptyEntries);
                            p = ch[0].Trim();
                            q = ch[1].Trim();
                            float od, horaire;
                            int jour;
                            if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                            {
                                od = Single.Parse(ch[2].Replace(',', '.'));
                                jour = (int)Single.Parse(ch[3].Replace(',', '.'));
                                horaire = Single.Parse(ch[4].Replace(',', '.'));
                            }
                            else
                            {
                                od = Single.Parse(ch[2].Replace('.', ','));
                                jour = (int)Single.Parse(ch[3].Replace('.', ','));
                                horaire = Single.Parse(ch[4].Replace('.', ','));
                            }
                            if (ch.Length > 5)
                            {
                                if (ch[5].ToLower() == "d")
                                {
                                    sens = 1;

                                }
                                else if (ch[5].ToLower() == "a")
                                {
                                    sens = 2;
                                }
                            }
                            else
                            {
                                sens = 1;
                            }
                            if (ch.Length > 6)
                            {
                                if (ch[6].Length == 0)
                                {
                                    libod = numod.ToString();

                                }
                                else
                                {
                                    libod = ch[6].Trim();
                                }
                                libod = ch[6];
                            }
                            else
                            {
                                libod = numod.ToString();
                            }
                            if (ch.Length > 17)
                            {
                                string[] type_delim = { "|" };
                                int k;
                                string[] scveh, scwait, scmap, scboa, scoef_tmap, stboa, stboa_max, stoll;
                                if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                                {
                                    scveh = ch[7].Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    scwait = ch[8].Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    scmap = ch[9].Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    scboa = ch[10].Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    scoef_tmap = ch[11].Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    stboa = ch[12].Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    stboa_max = ch[13].Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    //    stmap_max = ch[13].Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    stoll = ch[16].Replace(",", ".").Split(type_delim, StringSplitOptions.None);

                                }
                                else
                                {
                                    scveh = ch[7].Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    scwait = ch[8].Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    scmap = ch[9].Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    scboa = ch[10].Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    scoef_tmap = ch[11].Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    stboa = ch[12].Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    stboa_max = ch[13].Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    //  stmap_max = ch[13].Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    stoll = ch[16].Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                }
                                projet.param_affectation_horaire.texte_cveh = ch[7];
                                projet.param_affectation_horaire.texte_cwait = ch[8];
                                projet.param_affectation_horaire.texte_cmap = ch[9];
                                projet.param_affectation_horaire.texte_cboa = ch[10];
                                projet.param_affectation_horaire.texte_coef_tmap = ch[11];
                                projet.param_affectation_horaire.texte_tboa = ch[12];
                                projet.param_affectation_horaire.texte_tboa_max = ch[13];
                                //                        projet.param_affectation_horaire.texte_tboa_max = ch[12];
                                projet.param_affectation_horaire.texte_toll = ch[16];


                                //pondérations temps TC par type
                                for (k = 0; k < scveh.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = scveh[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.cveh["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.cveh[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //pondérations temps attente par type
                                for (k = 0; k < scwait.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = scwait[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.cwait["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.cwait[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //pondérations temps marche par type
                                for (k = 0; k < scmap.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = scmap[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.cmap["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.cmap[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //pondérations correspondance par type
                                for (k = 0; k < scboa.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = scboa[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.cboa["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.cboa[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //pondérations coef vitesse marche par type
                                for (k = 0; k < scoef_tmap.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = scoef_tmap[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.coef_tmap["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.coef_tmap[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //temps correspondance par type
                                for (k = 0; k < stboa.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = stboa[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.tboa["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.tboa[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //temps correspondance maximum par type
                                for (k = 0; k < stboa_max.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = stboa_max[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.tboa_max["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.tboa_max[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //pondération péage par type
                                for (k = 0; k < stoll.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = stoll[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.ctoll["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.ctoll[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }

                                foreach (String cle in types)
                                {
                                    if (projet.param_affectation_horaire.cveh.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.cveh[cle] = projet.param_affectation_horaire.cveh["0"];
                                    }
                                    if (projet.param_affectation_horaire.cmap.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.cmap[cle] = projet.param_affectation_horaire.cmap["0"];
                                    }
                                    if (projet.param_affectation_horaire.cwait.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.cwait[cle] = projet.param_affectation_horaire.cwait["0"];
                                    }
                                    if (projet.param_affectation_horaire.cboa.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.cboa[cle] = projet.param_affectation_horaire.cboa["0"];
                                    }
                                    if (projet.param_affectation_horaire.tboa.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.tboa[cle] = projet.param_affectation_horaire.tboa["0"];
                                    }
                                    if (projet.param_affectation_horaire.coef_tmap.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.coef_tmap[cle] = projet.param_affectation_horaire.coef_tmap["0"];
                                    }
                                    if (projet.param_affectation_horaire.tboa_max.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.tboa_max[cle] = projet.param_affectation_horaire.tboa_max["0"];
                                    }
                                    if (projet.param_affectation_horaire.ctoll.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.ctoll[cle] = projet.param_affectation_horaire.ctoll["0"];
                                    }
                                }
                                if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                                {
                                    projet.param_affectation_horaire.nb_jours = int.Parse(ch[14].Split(type_delim, StringSplitOptions.None)[0]);
                                    projet.param_affectation_horaire.tmapmax = float.Parse(ch[15].Replace(',', '.').Split(type_delim, StringSplitOptions.None)[0]);
                                    projet.param_affectation_horaire.temps_max = float.Parse(ch[17].Replace(',', '.').Split(type_delim, StringSplitOptions.None)[0]);

                                }
                                else
                                {
                                    projet.param_affectation_horaire.nb_jours = int.Parse(ch[14].Split(type_delim, StringSplitOptions.None)[0]);
                                    projet.param_affectation_horaire.tmapmax = float.Parse(ch[15].Replace('.', ',').Split(type_delim, StringSplitOptions.None)[0]);
                                    projet.param_affectation_horaire.temps_max = float.Parse(ch[17].Replace('.', ',').Split(type_delim, StringSplitOptions.None)[0]);

                                }

                                /*                        for (k = 0; k <= projet.reseaux[projet.reseau_actif].max_type; k++)
                                                        {



                                                            if (k < scveh.Length)
                                                            {
                                                                projet.param_affectation_horaire.cveh[k]= float.Parse(scveh[k]);
                                                            }
                                                            else
                                                            {
                                                                projet.param_affectation_horaire.cveh[k] = float.Parse(scveh[0]);
                                                            }
                                                            if (k < scwait.Length)
                                                            {
                                                                projet.param_affectation_horaire.cwait[k]= float.Parse(scwait[k]);
                                                            }
                                                            else
                                                            {
                                                                projet.param_affectation_horaire.cwait[k] = float.Parse(scwait[0]);
                                                            }
                                                            if (k < scmap.Length)
                                                            {
                                                                projet.param_affectation_horaire.cmap[k]= float.Parse(scmap[k]);
                                                            }
                                                            else
                                                            {
                                                                projet.param_affectation_horaire.cmap[k] = float.Parse(scmap[0]);
                                                            }
                                                            if (k < scboa.Length)
                                                            {
                                                                projet.param_affectation_horaire.cboa[k]= float.Parse(scboa[k]);
                                                            }
                                                            else
                                                            {
                                                                projet.param_affectation_horaire.cboa[k] = float.Parse(scboa[0]);
                                                            }
                                                            if (k < scoef_tmap.Length)
                                                            {
                                                                projet.param_affectation_horaire.coef_tmap[k]= float.Parse(scoef_tmap[k]);
                                                            }
                                                            else
                                                            {
                                                                projet.param_affectation_horaire.coef_tmap[k] = float.Parse(scoef_tmap[0]);
                                                            }
                                                            if (k < stboa.Length)
                                                            {
                                                                projet.param_affectation_horaire.tboa[k]= float.Parse(stboa[k]);
                                                            }
                                                            else
                                                            {
                                                                projet.param_affectation_horaire.tboa[k] = float.Parse(stboa[0]);
                                                            }
                                                            if (k < stboa_max.Length)
                                                            {
                                                                projet.param_affectation_horaire.tboa_max[k] = float.Parse(stboa_max[k]);
                                                            }
                                                            else
                                                            {
                                                                projet.param_affectation_horaire.tboa_max[k] = float.Parse(stboa_max[0]);
                                                            }
                                                            if (k < stoll.Length)
                                                            {
                                                                projet.param_affectation_horaire.ctoll[k] = float.Parse(stoll[k]);
                                                            }
                                                            else
                                                            {
                                                                projet.param_affectation_horaire.ctoll[k] = float.Parse(stoll[0]);
                                                            }
                                                            projet.param_affectation_horaire.nb_jours = int.Parse(ch[13].Split(type_delim, StringSplitOptions.None)[0]);
                                                            projet.param_affectation_horaire.tmapmax = int.Parse(ch[14].Split(type_delim, StringSplitOptions.None)[0]);


                                                        }*/

                            }
                            else
                            {
                                string[] type_delim = { "|" };
                                int k;
                                string[] scveh, scwait, scmap, scboa, scoef_tmap, stboa, stboa_max, stoll;
                                if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                                {
                                    scveh = aff_hor.texte_cveh.Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    scwait = aff_hor.texte_cwait.Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    scmap = aff_hor.texte_cmap.Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    scboa = aff_hor.texte_cboa.Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    scoef_tmap = aff_hor.texte_coef_tmap.Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    stboa = aff_hor.texte_tboa.Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    stboa_max = aff_hor.texte_tboa_max.Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                    stoll = aff_hor.texte_toll.Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                }
                                else
                                {
                                    scveh = aff_hor.texte_cveh.Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    scwait = aff_hor.texte_cwait.Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    scmap = aff_hor.texte_cmap.Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    scboa = aff_hor.texte_cboa.Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    scoef_tmap = aff_hor.texte_coef_tmap.Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    stboa = aff_hor.texte_tboa.Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    stboa_max = aff_hor.texte_tboa_max.Replace(".", ",").Split(type_delim, StringSplitOptions.None);
                                    stoll = aff_hor.texte_toll.Replace(",", ".").Split(type_delim, StringSplitOptions.None);
                                }



                                projet.param_affectation_horaire = aff_hor;
                                //pondérations temps TC par type
                                for (k = 0; k < scveh.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = scveh[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.cveh["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.cveh[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //pondérations temps attente par type
                                for (k = 0; k < scwait.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = scwait[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.cwait["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.cwait[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //pondérations temps marche par type
                                for (k = 0; k < scmap.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = scmap[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.cmap["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.cmap[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //pondérations correspondance par type
                                for (k = 0; k < scboa.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = scboa[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.cboa["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.cboa[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //pondérations coef vitesse marche par type
                                for (k = 0; k < scoef_tmap.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = scoef_tmap[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.coef_tmap["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.coef_tmap[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //temps correspondance par type
                                for (k = 0; k < stboa.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = stboa[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.tboa["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.tboa[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //temps correspondance maximum par type
                                for (k = 0; k < stboa_max.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = stboa_max[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.tboa_max["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.tboa_max[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }
                                //pondération péage par type
                                for (k = 0; k < stoll.Length; k++)
                                {
                                    string[] keys;
                                    string[] sep = { ":" };
                                    keys = stoll[k].Split(sep, StringSplitOptions.None);
                                    if (keys.Length == 1)
                                    {
                                        projet.param_affectation_horaire.ctoll["0"] = float.Parse(keys[0]);
                                    }
                                    else
                                    {
                                        projet.param_affectation_horaire.ctoll[keys[0].Trim()] = float.Parse(keys[1]);
                                    }
                                }

                                foreach (String cle in types)
                                {
                                    if (projet.param_affectation_horaire.cveh.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.cveh[cle] = projet.param_affectation_horaire.cveh["0"];
                                    }
                                    if (projet.param_affectation_horaire.cmap.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.cmap[cle] = projet.param_affectation_horaire.cmap["0"];
                                    }
                                    if (projet.param_affectation_horaire.cwait.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.cwait[cle] = projet.param_affectation_horaire.cwait["0"];
                                    }
                                    if (projet.param_affectation_horaire.cboa.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.cboa[cle] = projet.param_affectation_horaire.cboa["0"];
                                    }
                                    if (projet.param_affectation_horaire.tboa.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.tboa[cle] = projet.param_affectation_horaire.tboa["0"];
                                    }
                                    if (projet.param_affectation_horaire.coef_tmap.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.coef_tmap[cle] = projet.param_affectation_horaire.coef_tmap["0"];
                                    }
                                    if (projet.param_affectation_horaire.tboa_max.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.tboa_max[cle] = projet.param_affectation_horaire.tboa_max["0"];
                                    }
                                    if (projet.param_affectation_horaire.ctoll.ContainsKey(cle) == false)
                                    {
                                        projet.param_affectation_horaire.ctoll[cle] = projet.param_affectation_horaire.ctoll["0"];
                                    }
                                }


                                /*                            for (k = 0; k <= projet.reseaux[projet.reseau_actif].max_type; k++)
                                                            {


                                                                if (k < scveh.Length)
                                                                {
                                                                    projet.param_affectation_horaire.cveh[k]= float.Parse(scveh[k]);
                                                                }
                                                                else
                                                                {
                                                                    projet.param_affectation_horaire.cveh[k]=float.Parse(scveh[0]);
                                                                }
                                                                if (k <scwait.Length)
                                                                {
                                                                    projet.param_affectation_horaire.cwait[k]= float.Parse(scwait[k]);
                                                                }
                                                                else
                                                                {
                                                                    projet.param_affectation_horaire.cwait[k]= float.Parse(scwait[0]);
                                                                }
                                                                if (k < scmap.Length)
                                                                {
                                                                    projet.param_affectation_horaire.cmap[k]= float.Parse(scmap[k]);
                                                                }
                                                                else
                                                                {
                                                                    projet.param_affectation_horaire.cmap[k]= float.Parse(scmap[0]);
                                                                }
                                                                if (k < scboa.Length)
                                                                {
                                                                    projet.param_affectation_horaire.cboa[k]= float.Parse(scboa[k]);
                                                                }
                                                                else
                                                                {
                                                                    projet.param_affectation_horaire.cboa[k]= float.Parse(scboa[0]);
                                                                }
                                                                if (k < scoef_tmap.Length)
                                                                {
                                                                    projet.param_affectation_horaire.coef_tmap[k]= float.Parse(scoef_tmap[k]);
                                                                }
                                                                else
                                                                {
                                                                    projet.param_affectation_horaire.coef_tmap[k]= float.Parse(scoef_tmap[0]);
                                                                }
                                                                if (k < stboa.Length)
                                                                {
                                                                    projet.param_affectation_horaire.tboa[k]= float.Parse(stboa[k]);
                                                                }
                                                                else
                                                                {
                                                                    projet.param_affectation_horaire.tboa[k]=float.Parse(stboa[0]);                                
                                                                }
                                                                if (k < stboa_max.Length)
                                                                {
                                                                    projet.param_affectation_horaire.tboa_max[k] = float.Parse(stboa_max[k]);
                                                                }
                                                                else
                                                                {
                                                                    projet.param_affectation_horaire.tboa_max[k] = float.Parse(stboa_max[0]);
                                                                }
                                                                if (k < stoll.Length)
                                                                {
                                                                    projet.param_affectation_horaire.ctoll[k] = float.Parse(stoll[k]);
                                                                }
                                                                else
                                                                {
                                                                    projet.param_affectation_horaire.ctoll[k] = float.Parse(stoll[0]);
                                                                }

                                                            }

                                                            */


                            }
                            if (ch.Length > 23)
                            {
                                if (System.Globalization.NumberFormatInfo.CurrentInfo.NumberDecimalSeparator == ".")
                                {
                                    projet.param_affectation_horaire.sortie_chemins = bool.Parse(ch[18].Replace(",", "."));
                                    projet.param_affectation_horaire.sortie_temps = int.Parse(ch[19].Replace(",", "."));
                                    projet.param_affectation_horaire.algorithme = int.Parse(ch[20].Replace(",", "."));
                                    projet.param_affectation_horaire.param_dijkstra = float.Parse(ch[21].Replace(",", "."));
                                    projet.param_affectation_horaire.max_nb_buckets = float.Parse(ch[22].Replace(",", "."));
                                    projet.param_affectation_horaire.pu = float.Parse(ch[23].Replace(",", "."));
                                }
                                else
                                {
                                    projet.param_affectation_horaire.sortie_chemins = bool.Parse(ch[18].Replace(".", ","));
                                    projet.param_affectation_horaire.sortie_temps = int.Parse(ch[19].Replace(".", ","));
                                    projet.param_affectation_horaire.algorithme = int.Parse(ch[20].Replace(".", ","));
                                    projet.param_affectation_horaire.param_dijkstra = float.Parse(ch[21].Replace(".", ","));
                                    projet.param_affectation_horaire.max_nb_buckets = float.Parse(ch[22].Replace(".", ","));
                                    projet.param_affectation_horaire.pu = float.Parse(ch[23].Replace(".", ","));

                                }

                            }
                            else
                            {
                                projet.param_affectation_horaire.sortie_chemins = aff_hor.sortie_chemins;
                                projet.param_affectation_horaire.sortie_temps = aff_hor.sortie_temps;
                                projet.param_affectation_horaire.algorithme = aff_hor.algorithme;
                                projet.param_affectation_horaire.param_dijkstra = aff_hor.param_dijkstra;
                                projet.param_affectation_horaire.max_nb_buckets = aff_hor.max_nb_buckets;
                                projet.param_affectation_horaire.pu = aff_hor.pu;
                                
                            }


                            if (ch.Length > 24)
                            {
                                projet.param_affectation_horaire.texte_filtre_sortie = ch[24];
                            }
                            //MessageBox.Show(p.ToString() + " " + q.ToString() + " " + horaire.ToString());
                            //avancement.textBox1.Text = p.ToString() + " " + q.ToString() + " " + horaire.ToString();
                            //                        avancement.textBox1.Text = flux.Position;
                            //             fich_sortie.WriteLine(pivot.ToString() + projet.reseaux[projet.reseaux].links[pivot].cout.ToString());
                            //                flux.Position += chaine.Length;


                            HashSet<String> filtre = new HashSet<String>();

                            if (projet.param_affectation_horaire.texte_filtre_sortie.Trim().Length > 0)
                            {
                                ch = projet.param_affectation_horaire.texte_filtre_sortie.Split('|');

                                for (int f = 0; f < ch.Length; f++)
                                {
                                    if (filtre.Contains(ch[f].Trim()) == false)

                                        filtre.Add(ch[f].Trim());
                                }
                            }


                            //sens heure de départ//
                            //sens heure de départ//
                            //sens heure de départ//
                            //sens heure de départ//
                            //sens heure de départ//


                            //if (projet.reseaux[projet.reseau_actif].matrices[0].o[p].d.Count > 0)
                            if (sens == 1)
                            {
                                if (p1 == p && jour1 == jour && horaire1 == horaire && sens1 == sens && ch.Length < 13)
                                {
                                    q1 = q;

                                    goto fin_gga;
                                }
                                p1 = p; q1 = q; jour1 = jour; horaire1 = horaire; sens1 = sens;
                                for (i = 0; i < projet.reseaux[projet.reseau_actif].links.Count; i++)
                                {
                                    projet.reseaux[projet.reseau_actif].links[i].pole = "-1";
                                    projet.reseaux[projet.reseau_actif].links[i].touche = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].cout = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].tatt = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].tatt1 = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].tcor = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].ncorr = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].tmap = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].tveh = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].h = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].ttoll = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].l = 0;
                                    for (j = 0; j < projet.reseaux[projet.reseau_actif].links[i].services.Count; j++)
                                    {
                                        projet.reseaux[projet.reseau_actif].links[i].services[j].delta = 0;
                                        projet.reseaux[projet.reseau_actif].links[i].services[j].alij = 0;
                                        projet.reseaux[projet.reseau_actif].links[i].services[j].boai = 0;
                                    }
                                    projet.reseaux[projet.reseau_actif].links[i].pivot = -1;
                                    projet.reseaux[projet.reseau_actif].links[i].turn_pivot = -1;
                                    projet.reseaux[projet.reseau_actif].links[i].service = -1;
                                    projet.reseaux[projet.reseau_actif].links[i].is_queue = false;





                                }
                                gga_nq.Clear();
                                string depart = p;
                                int pivot = -1, value;
                                int successeur, bucket, id_bucket = 0;
                                String succ_type;
                                float penalite = 0, temps_correspondance, max_correspondance;

                                if (projet.reseaux[projet.reseau_actif].numnoeud.TryGetValue(p, out value) == true)
                                {
                                    for (j = 0; j < projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].numnoeud[depart]].succ.Count; j++)
                                    {
                                        successeur = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].numnoeud[depart]].succ[j];
                                        succ_type = projet.reseaux[projet.reseau_actif].links[successeur].type;
                                        max_correspondance = projet.param_affectation_horaire.tboa_max[succ_type];





                                        if (projet.reseaux[projet.reseau_actif].links[successeur].ligne < 0 && projet.param_affectation_horaire.cmap[succ_type] > 0 && projet.reseaux[projet.reseau_actif].links[successeur].temps < projet.param_affectation_horaire.tmapmax)
                                        {
                                            bool test_periode = false;

                                            if (projet.reseaux[projet.reseau_actif].links[successeur].services.Count > 0)
                                            {
                                                int decal_jour = (int)Math.Floor(horaire / 1440f);
                                                int kk;
                                                for (kk = 0; kk < projet.reseaux[projet.reseau_actif].links[successeur].services.Count; kk++)
                                                {
                                                    if (decal_jour <= projet.param_affectation_horaire.nb_jours)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[kk].regime].Substring(jour + decal_jour, 1) == "O" && projet.reseaux[projet.reseau_actif].links[successeur].services[kk].hd + 1440f * decal_jour <= horaire && projet.reseaux[projet.reseau_actif].links[successeur].services[kk].hf + 1440f * decal_jour > horaire)
                                                        {
                                                            test_periode = true;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].service = kk;
                                                        }
                                                    }
                                                }

                                            }
                                            else
                                            {
                                                test_periode = true;
                                            }
                                            //touches.Enqueue(successeur);

                                            if (test_periode == true)
                                            {
                                                projet.reseaux[projet.reseau_actif].links[successeur].touche = 1;
                                                projet.reseaux[projet.reseau_actif].links[successeur].cout = projet.reseaux[projet.reseau_actif].links[successeur].temps * projet.param_affectation_horaire.coef_tmap[succ_type] * projet.param_affectation_horaire.cmap[succ_type] + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type];
                                                projet.reseaux[projet.reseau_actif].links[successeur].l = projet.reseaux[projet.reseau_actif].links[successeur].longueur;
                                                projet.reseaux[projet.reseau_actif].links[successeur].tmap = projet.reseaux[projet.reseau_actif].links[successeur].temps * projet.param_affectation_horaire.coef_tmap[succ_type];
                                                projet.reseaux[projet.reseau_actif].links[successeur].ttoll = projet.reseaux[projet.reseau_actif].links[successeur].toll;
                                                projet.reseaux[projet.reseau_actif].links[successeur].h = horaire + projet.reseaux[projet.reseau_actif].links[successeur].temps * projet.param_affectation_horaire.coef_tmap[succ_type];
                                                projet.reseaux[projet.reseau_actif].links[successeur].pivot = -1;
                                                projet.reseaux[projet.reseau_actif].links[successeur].turn_pivot = -1;
                                                projet.reseaux[projet.reseau_actif].links[successeur].pole = depart;
                                                //bucket = Convert.ToInt32(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout, 2) / projet.param_affectation_horaire.param_dijkstra)), projet.param_affectation_horaire.max_nb_buckets);
                                                bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));

                                                while (bucket >= gga_nq.Count)
                                                {
                                                    gga_nq.Add(new List<int>());
                                                }
                                                gga_nq[bucket].Add(successeur);
                                                projet.param_affectation_horaire.nb_pop++;

                                            }
                                        }
                                        else if (projet.param_affectation_horaire.cveh[succ_type] > 0)
                                        {
                                            int ii, jj, num_service = -1, h3 = 0, delta, duree_periode;
                                            float h1 = 1e38f, h2 = 1e38f, cout2 = 1e38f;
                                            for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[successeur].services.Count; ii++)
                                            {
                                                delta = 0;
                                                duree_periode = projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[ii].regime].Length;
                                                if ((projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f < horaire) || projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[ii].regime].Substring(jour, 1) == "N")
                                                {

                                                    h1 = 1e38f;
                                                    h2 = 1e38f;
                                                    h3 = -1;
                                                    for (jj = jour + 1; jj <= Math.Min(jour + projet.param_affectation_horaire.nb_jours, duree_periode - 1); jj++)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[ii].regime].Substring(jj, 1) == "O" && (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + (-jour + jj) * 24f * 60f < h1))
                                                        {
                                                            h1 = projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + (-jour + jj) * 24f * 60f;
                                                            h2 = (-jour + jj);
                                                            h3 = jj;
                                                        }

                                                    }
                                                    if (h3 != -1)
                                                    {
                                                        projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta = h2;
                                                    }
                                                    else
                                                    {
                                                        delta = -1;
                                                    }


                                                }


                                                if (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f - horaire < max_correspondance)
                                                {
                                                    if (((projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd) * projet.param_affectation_horaire.cveh[succ_type] + (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f - horaire) * projet.param_affectation_horaire.cwait[succ_type]) + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type] < cout2 && delta > -1)
                                                    {
                                                        cout2 = (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd) * projet.param_affectation_horaire.cveh[succ_type] + (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f - horaire) * projet.param_affectation_horaire.cwait[succ_type] + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type];
                                                        num_service = ii;

                                                    }
                                                }

                                            }
                                            if (num_service != -1)
                                            {
                                                projet.reseaux[projet.reseau_actif].links[successeur].service = num_service;
                                                projet.reseaux[projet.reseau_actif].links[successeur].cout = (projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd) * projet.param_affectation_horaire.cveh[succ_type] + (projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].delta * 1440f - horaire) * projet.param_affectation_horaire.cwait[succ_type] + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type];

                                                projet.reseaux[projet.reseau_actif].links[successeur].touche = 1;

                                                projet.reseaux[projet.reseau_actif].links[successeur].h = projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f;

                                                //                                    projet.reseaux[projet.reseau_actif].links[successeur].tatt = projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta - projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                projet.reseaux[projet.reseau_actif].links[successeur].tatt = projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f - horaire;
                                                projet.reseaux[projet.reseau_actif].links[successeur].tatt1 = projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f - horaire;

                                                projet.reseaux[projet.reseau_actif].links[successeur].tveh = projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hd;
                                                projet.reseaux[projet.reseau_actif].links[successeur].tcor = 0;
                                                projet.reseaux[projet.reseau_actif].links[successeur].ncorr = 1;
                                                projet.reseaux[projet.reseau_actif].links[successeur].tmap = 0;
                                                projet.reseaux[projet.reseau_actif].links[successeur].ttoll = projet.reseaux[projet.reseau_actif].links[successeur].toll;
                                                projet.reseaux[projet.reseau_actif].links[successeur].l = projet.reseaux[projet.reseau_actif].links[successeur].longueur;
                                                //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));

                                                while (bucket >= gga_nq.Count)
                                                {
                                                    gga_nq.Add(new List<int>());
                                                }
                                                gga_nq[bucket].Add(successeur);
                                                projet.param_affectation_horaire.nb_pop++;
                                                //                                touches.Enqueue(successeur);
                                                projet.reseaux[projet.reseau_actif].links[successeur].pivot = -1;
                                                projet.reseaux[projet.reseau_actif].links[successeur].turn_pivot = -1;
                                                projet.reseaux[projet.reseau_actif].links[successeur].pole = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[successeur].no].i;
                                            }
                                        }

                                    }
                                }
                                else
                                {
                                    fich_log.WriteLine("OD error " + libod + ":" + chaine + ": non existing origin node!");
                                }
                                int bucket_cout_max = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.param_affectation_horaire.temps_max / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                //         MessageBox.Show(projet.param_affectation_horaire.algorithme.ToString());
                                while (gga_nq.Count > id_bucket && bucket_cout_max > id_bucket)
                                {

                                    while (gga_nq[id_bucket].Count == 0)
                                    {
                                        id_bucket++;
                                        if (id_bucket == gga_nq.Count || id_bucket== bucket_cout_max)
                                        {
                                            goto fin_gga;
                                        }
                                    }

                                    if (projet.param_affectation_horaire.algorithme == 0)
                                    {
                                        pivot = gga_nq[id_bucket][0];
                                        gga_nq[id_bucket].RemoveAt(0);
                                    }
                                    else
                                    {
                                        int k, id_pivot = -1; double cout_max = 1e38f;
                                        for (k = 0; k < gga_nq[id_bucket].Count; k++)
                                        {
                                            if (projet.reseaux[projet.reseau_actif].links[gga_nq[id_bucket][k]].cout < cout_max)
                                            {
                                                cout_max = projet.reseaux[projet.reseau_actif].links[gga_nq[id_bucket][k]].cout;
                                                id_pivot = k;
                                            }
                                        }
                                        pivot = gga_nq[id_bucket][id_pivot];
                                        gga_nq[id_bucket].RemoveAt(id_pivot);
                                        projet.reseaux[projet.reseau_actif].links[pivot].touche = 3;
                                    }



                                    //avancement.textBox1.Text = touches.Count.ToString() + " " + calcules.Count.ToString() + " " + projet.reseaux[projet.reseau_actif].links[pivot].cout;
                                    //avancement.textBox1.Refresh();
                                    for (j = 0; j < projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[pivot].nd].succ.Count; j++)
                                    {
                                        link troncon_succ = projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[pivot].nd].succ[j]];
                                        link troncon_pivot = projet.reseaux[projet.reseau_actif].links[pivot];
                                        successeur = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[pivot].nd].succ[j];
                                        succ_type = projet.reseaux[projet.reseau_actif].links[successeur].type;

                                        if (projet.param_affectation_horaire.demitours == true)
                                        {

                                            if (troncon_pivot.no == troncon_succ.nd)
                                            { 
                                                penalite = -1;
                                            }
                                            else
                                            {
                                                penalite = 0;
                                            }
                                        }
                                        else
                                        {
                                            penalite = 0;
                                        }

                                        Turn virage = new Turn();
                                        virage.arci = pivot;
                                        virage.arcj = successeur;
                                        float value2;
                                        if (projet.reseaux[projet.reseau_actif].nodes[troncon_pivot.nd].is_intersection == true)
                                        {
                                            if (turns.TryGetValue(virage, out value2) == true)
                                            {
                                                penalite = turns[virage];
                                            }
                                            else
                                            {
                                                penalite = 0;
                                            }
                                        }

                                        if (penalite >= 0)
                                        {
                                            if (penalite > 0)
                                            {
                                                temps_correspondance = penalite;
                                                max_correspondance = projet.param_affectation_horaire.tboa_max[succ_type];

                                            }
                                            else
                                            {
                                                temps_correspondance = projet.param_affectation_horaire.tboa[succ_type];
                                                max_correspondance = projet.param_affectation_horaire.tboa_max[succ_type];
                                            }
                                            //successeurs touches pour la première fois
                                            if (projet.reseaux[projet.reseau_actif].links[successeur].touche == 0)
                                            {
                                                // successeur marche à pied
                                                if (projet.reseaux[projet.reseau_actif].links[successeur].ligne < 0 && projet.param_affectation_horaire.cmap[succ_type] > 0 && projet.reseaux[projet.reseau_actif].links[pivot].tmap + projet.reseaux[projet.reseau_actif].links[successeur].temps < projet.param_affectation_horaire.tmapmax)
                                                {
                                                    bool test_periode = false;
                                                    projet.reseaux[projet.reseau_actif].links[successeur].service = -1;
                                                    if (projet.reseaux[projet.reseau_actif].links[successeur].services.Count > 0)
                                                    {
                                                        int decal_jour = (int)(Math.Floor((projet.reseaux[projet.reseau_actif].links[pivot].h + penalite) / 1440f));
                                                        for (int kk = 0; kk < projet.reseaux[projet.reseau_actif].links[successeur].services.Count; kk++)
                                                        {
                                                            if (decal_jour <= projet.param_affectation_horaire.nb_jours)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[kk].regime].Substring(jour + decal_jour, 1) == "O" && projet.reseaux[projet.reseau_actif].links[successeur].services[kk].hd + 1440f * decal_jour <= projet.reseaux[projet.reseau_actif].links[pivot].h + penalite && projet.reseaux[projet.reseau_actif].links[successeur].services[kk].hf + 1440f * decal_jour > projet.reseaux[projet.reseau_actif].links[pivot].h + penalite)
                                                                {
                                                                    test_periode = true;
                                                                    projet.reseaux[projet.reseau_actif].links[successeur].service = kk;
                                                                }
                                                            }
                                                        }

                                                    }
                                                    else
                                                    {
                                                        test_periode = true;
                                                    }

                                                    if (test_periode == true)
                                                    {
                                                        projet.reseaux[projet.reseau_actif].links[successeur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].temps + penalite) * projet.param_affectation_horaire.coef_tmap[succ_type] * projet.param_affectation_horaire.cmap[succ_type]/*+ projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type]*/;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].h = projet.reseaux[projet.reseau_actif].links[pivot].h + (projet.reseaux[projet.reseau_actif].links[successeur].temps) * projet.param_affectation_horaire.coef_tmap[succ_type] + penalite;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor;

                                                        projet.reseaux[projet.reseau_actif].links[successeur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap + (penalite + projet.reseaux[projet.reseau_actif].links[successeur].temps) * projet.param_affectation_horaire.coef_tmap[succ_type];
                                                        projet.reseaux[projet.reseau_actif].links[successeur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[successeur].toll;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].touche = 1;

                                                        projet.reseaux[projet.reseau_actif].links[successeur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[successeur].longueur;


                                                        //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                        bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));

                                                        while (bucket >= gga_nq.Count)
                                                        {
                                                            gga_nq.Add(new List<int>());
                                                        }
                                                        gga_nq[bucket].Add(successeur);
                                                        projet.param_affectation_horaire.nb_pop++;
                                                        //                                        touches.Enqueue(successeur);
                                                        projet.reseaux[projet.reseau_actif].links[successeur].pivot = pivot;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].turn_pivot = j;

                                                        projet.reseaux[projet.reseau_actif].links[successeur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                                    }
                                                }
                                                //successeur TC même ligne
                                                else if (projet.reseaux[projet.reseau_actif].links[successeur].ligne == projet.reseaux[projet.reseau_actif].links[pivot].ligne && projet.param_affectation_horaire.cveh[succ_type] > 0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0)
                                                {
                                                    int ii, num_service = -1;
                                                    for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[successeur].services.Count; ii++)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].numero == projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].numero)
                                                        {
                                                            if (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd >= projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].hf)
                                                            {
                                                                num_service = ii;
                                                            }
                                                        }
                                                    }
                                                    //                                                if (num_service != -1 && projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd + projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].delta * 1440f >= projet.reseaux[projet.reseau_actif].links[pivot].h)
                                                    if (num_service != -1 && projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd >= projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].hf)
                                                    {
                                                        projet.reseaux[projet.reseau_actif].links[successeur].service = num_service;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].delta = projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].delta;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].touche = 1;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cveh[succ_type] + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type];
                                                        projet.reseaux[projet.reseau_actif].links[successeur].h = projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[successeur].longueur;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[successeur].toll;

                                                        bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));

                                                        //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                        while (bucket >= gga_nq.Count)
                                                        {
                                                            gga_nq.Add(new List<int>());
                                                        }
                                                        gga_nq[bucket].Add(successeur);
                                                        projet.param_affectation_horaire.nb_pop++;
                                                        //touches.Enqueue(successeur);
                                                        projet.reseaux[projet.reseau_actif].links[successeur].pivot = pivot;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].turn_pivot = j;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                                    }
                                                }

                                                //successeur TC lignes différentes
                                                else if (projet.reseaux[projet.reseau_actif].links[successeur].ligne != projet.reseaux[projet.reseau_actif].links[pivot].ligne && projet.param_affectation_horaire.cveh[succ_type] > 0 && projet.reseaux[projet.reseau_actif].links[successeur].ligne > 0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0)
                                                {
                                                    int ii, jj, num_service = -1, h3 = 0, duree_periode, delta;
                                                    float h1 = 1e38f, h2 = 1e38f, cout2 = 1e38f;

                                                    for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[successeur].services.Count; ii++)
                                                    {
                                                        delta = 0;

                                                        duree_periode = projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[ii].regime].Length;

                                                        if ((projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f < projet.reseaux[projet.reseau_actif].links[pivot].h + temps_correspondance) || projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[ii].regime].Substring(jour, 1) == "N")
                                                        {

                                                            h1 = 1e38f;
                                                            h2 = 1e38f;
                                                            h3 = -1;
                                                            for (jj = jour + 1; jj <= Math.Min(jour + projet.param_affectation_horaire.nb_jours, duree_periode - 1); jj++)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[ii].regime].Substring(jj, 1) == "O" && (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + (-jour + jj) * 24f * 60f < h1) && (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + (-jour + jj) * 24f * 60f) - temps_correspondance > projet.reseaux[projet.reseau_actif].links[pivot].h)
                                                                {
                                                                    h1 = projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + (-jour + jj) * 24f * 60f;
                                                                    h2 = (-jour + jj);
                                                                    h3 = jj;
                                                                }

                                                            }
                                                            if (h3 != -1)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta > h2 || projet.reseaux[projet.reseau_actif].links[successeur].touche == 0)
                                                                {
                                                                    projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta = h2;
                                                                }
                                                            }
                                                            else
                                                            {
                                                                delta = -1;
                                                            }


                                                        }


                                                        if ((projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f < projet.reseaux[projet.reseau_actif].links[pivot].h + max_correspondance) && (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f >= projet.reseaux[projet.reseau_actif].links[pivot].h + temps_correspondance))

                                                        {
                                                            if (projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd) * projet.param_affectation_horaire.cveh[succ_type] + (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[succ_type] + temps_correspondance * projet.param_affectation_horaire.cboa[succ_type] + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type] < cout2 && delta > -1)
                                                            {
                                                                cout2 = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd) * projet.param_affectation_horaire.cveh[succ_type] + (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[succ_type] + temps_correspondance * projet.param_affectation_horaire.cboa[succ_type] + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type];
                                                                num_service = ii;

                                                            }
                                                        }

                                                    }
                                                    if (num_service != -1)
                                                    {
                                                        projet.reseaux[projet.reseau_actif].links[successeur].service = num_service;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd) * projet.param_affectation_horaire.cveh[succ_type] + (projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[succ_type] + (temps_correspondance * projet.param_affectation_horaire.cboa[succ_type]) + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type];

                                                        projet.reseaux[projet.reseau_actif].links[successeur].touche = 1;

                                                        projet.reseaux[projet.reseau_actif].links[successeur].h = projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f;
                                                        if (projet.reseaux[projet.reseau_actif].links[pivot].ncorr == 0)
                                                        {
                                                            projet.reseaux[projet.reseau_actif].links[successeur].tatt1 = projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                        }
                                                        else
                                                        {
                                                            projet.reseaux[projet.reseau_actif].links[successeur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                        }


                                                        projet.reseaux[projet.reseau_actif].links[successeur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hd;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor + temps_correspondance;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr + 1;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[successeur].longueur;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[successeur].toll;

                                                        //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                        bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                        while (bucket >= gga_nq.Count)
                                                        {
                                                            gga_nq.Add(new List<int>());
                                                        }
                                                        gga_nq[bucket].Add(successeur);
                                                        projet.param_affectation_horaire.nb_pop++;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].pivot = pivot;
                                                        projet.reseaux[projet.reseau_actif].links[successeur].turn_pivot = j;

                                                        if (projet.reseaux[projet.reseau_actif].links[pivot].pole == depart)
                                                        {
                                                            projet.reseaux[projet.reseau_actif].links[successeur].pole = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[successeur].no].i;
                                                        }
                                                        else
                                                        {
                                                            projet.reseaux[projet.reseau_actif].links[successeur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                                        }
                                                        /* if (projet.reseaux[projet.reseau_actif].links[successeur].tveh < 0)
                                                         {
                                                             //fich_sortie.WriteLine("30 " + pivot.ToString() + " " + projet.reseaux[projet.reseau_actif].links[pivot].cout.ToString() + " " + projet.reseaux[projet.reseau_actif].links[successeur].cout.ToString() + " " + projet.reseaux[projet.reseau_actif].links[pivot].ligne.ToString() + " " + projet.reseaux[projet.reseau_actif].links[successeur].ligne.ToString() + " " + projet.reseaux[projet.reseau_actif].links[pivot].h.ToString() + " " + projet.reseaux[projet.reseau_actif].links[successeur].h.ToString());
                                                         }*/
                                                    }
                                                }
                                            }


                                            //eléments déjà touchés
                                            else if (projet.reseaux[projet.reseau_actif].links[successeur].touche == 1 || projet.reseaux[projet.reseau_actif].links[successeur].touche == 2)
                                            {
                                                int id_service = -1;
                                                //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                //bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                //successeurs marche à pied
                                                if (projet.reseaux[projet.reseau_actif].links[successeur].ligne < 0 && projet.param_affectation_horaire.cmap[succ_type] > 0 && projet.reseaux[projet.reseau_actif].links[pivot].tmap + projet.reseaux[projet.reseau_actif].links[successeur].temps < projet.param_affectation_horaire.tmapmax)
                                                {
                                                    bool test_periode = false;

                                                    if (projet.reseaux[projet.reseau_actif].links[successeur].services.Count > 0)
                                                    {
                                                        int decal_jour = (int)(Math.Floor((projet.reseaux[projet.reseau_actif].links[pivot].h + penalite) / 1440f));
                                                        for (int kk = 0; kk < projet.reseaux[projet.reseau_actif].links[successeur].services.Count; kk++)
                                                        {
                                                            if (decal_jour <= projet.param_affectation_horaire.nb_jours)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[kk].regime].Substring(jour + decal_jour, 1) == "O" && projet.reseaux[projet.reseau_actif].links[successeur].services[kk].hd + 1440f * decal_jour <= projet.reseaux[projet.reseau_actif].links[pivot].h + penalite && projet.reseaux[projet.reseau_actif].links[successeur].services[kk].hf + 1440f * decal_jour > projet.reseaux[projet.reseau_actif].links[pivot].h + penalite)
                                                                {
                                                                    test_periode = true;
                                                                    id_service = kk;

                                                                }
                                                            }
                                                        }

                                                    }
                                                    else
                                                    {
                                                        test_periode = true;
                                                    }
                                                    if (test_periode == true)
                                                    {

                                                        if (projet.reseaux[projet.reseau_actif].links[successeur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout + (penalite + projet.reseaux[projet.reseau_actif].links[successeur].temps) * projet.param_affectation_horaire.coef_tmap[succ_type] * projet.param_affectation_horaire.cmap[succ_type] + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type])
                                                        {
                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Remove(successeur);
                                                            projet.reseaux[projet.reseau_actif].links[successeur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].temps + penalite) * projet.param_affectation_horaire.coef_tmap[succ_type] * projet.param_affectation_horaire.cmap[succ_type] + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type];
                                                            projet.reseaux[projet.reseau_actif].links[successeur].h = projet.reseaux[projet.reseau_actif].links[pivot].h + (projet.reseaux[projet.reseau_actif].links[successeur].temps) * projet.param_affectation_horaire.coef_tmap[succ_type] + penalite;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap + (penalite + projet.reseaux[projet.reseau_actif].links[successeur].temps) * projet.param_affectation_horaire.coef_tmap[succ_type];
                                                            projet.reseaux[projet.reseau_actif].links[successeur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[successeur].toll;

                                                            projet.reseaux[projet.reseau_actif].links[successeur].touche = 2;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[successeur].longueur;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].pivot = pivot;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].turn_pivot = j;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;

                                                            projet.reseaux[projet.reseau_actif].links[successeur].service = id_service;                                                        //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), ;
                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Add(successeur);
                                                            projet.param_affectation_horaire.nb_pop++;
                                                        }
                                                    }

                                                }
                                                //successeurs TC même ligne
                                                else if ((projet.reseaux[projet.reseau_actif].links[successeur].ligne == projet.reseaux[projet.reseau_actif].links[pivot].ligne && projet.param_affectation_horaire.cveh[succ_type] > 0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0 && projet.reseaux[projet.reseau_actif].links[successeur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout))
                                                {
                                                    int ii, num_service = -1;
                                                    for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[successeur].services.Count; ii++)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].numero == projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].numero)
                                                        {
                                                            if (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd >= projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].hf)
                                                            {
                                                                num_service = ii;
                                                            }
                                                        }


                                                    }

                                                    if (num_service != -1)
                                                    {
                                                        //                                                    if (projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd + projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].delta * 1440f >= projet.reseaux[projet.reseau_actif].links[pivot].h)
                                                        if (projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd >= projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].hf)
                                                        {

                                                            if (projet.reseaux[projet.reseau_actif].links[successeur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hf + projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cveh[succ_type] + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type] && projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd >= projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].hf)
                                                            {
                                                                bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                                gga_nq[bucket].Remove(successeur);
                                                                projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].delta = projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].delta;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].service = num_service;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].touche = 2;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cveh[succ_type] + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type];
                                                                projet.reseaux[projet.reseau_actif].links[successeur].h = projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf /* + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f */- projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[successeur].longueur;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[successeur].toll;

                                                                projet.reseaux[projet.reseau_actif].links[successeur].pivot = pivot;

                                                                projet.reseaux[projet.reseau_actif].links[successeur].turn_pivot = j;
                                                                projet.reseaux[projet.reseau_actif].links[successeur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                                                //bucket = Convert.ToInt32(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                                bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                                gga_nq[bucket].Add(successeur);
                                                                projet.param_affectation_horaire.nb_pop++;
                                                            }
                                                        }
                                                    }
                                                }
                                                //successeurs TC lignes différentes
                                                else if ((projet.reseaux[projet.reseau_actif].links[successeur].ligne != projet.reseaux[projet.reseau_actif].links[pivot].ligne) && projet.reseaux[projet.reseau_actif].links[successeur].ligne>0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0 && projet.param_affectation_horaire.cveh[succ_type] > 0 && projet.reseaux[projet.reseau_actif].links[successeur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout)//&& (projet.reseaux[projet.reseau_actif].links[pivot].h + projet.param_affectation_horaire.tboa < projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta*1440f))
                                                {
                                                    int ii, jj, num_service = -1, h3 = -1, duree_periode, delta;
                                                    float h1 = 1e38f, h2 = 1e38f, cout2 = 1e38f;
                                                    for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[successeur].services.Count; ii++)
                                                    {
                                                        delta = 0;
                                                        //projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta = 0;
                                                        duree_periode = projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[ii].regime].Length;

                                                        if ((projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f < projet.reseaux[projet.reseau_actif].links[pivot].h + temps_correspondance) || projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[ii].regime].Substring(jour, 1) == "N")
                                                        {

                                                            h1 = 1e38f;
                                                            h2 = 1e38f;
                                                            h3 = -1;
                                                            for (jj = jour + 1; jj <= Math.Min(jour + projet.param_affectation_horaire.nb_jours, duree_periode - 1); jj++)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[successeur].services[ii].regime].Substring(jj, 1) == "O" && (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + (-jour + jj) * 24f * 60f) < h1 && (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + (-jour + jj) * 24f * 60f - temps_correspondance) > projet.reseaux[projet.reseau_actif].links[pivot].h)
                                                                {
                                                                    h1 = projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + (-jour + jj) * 24f * 60f;
                                                                    h2 = (-jour + jj);
                                                                    h3 = jj;
                                                                }

                                                            }
                                                            if (h3 != -1)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta < h2 || projet.reseaux[projet.reseau_actif].links[successeur].touche == 0)
                                                                {
                                                                    projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta = h2;
                                                                }


                                                            }
                                                            else
                                                            {
                                                                delta = -1;
                                                            }


                                                        }
                                                        if ((projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f < projet.reseaux[projet.reseau_actif].links[pivot].h + max_correspondance) && (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f >= projet.reseaux[projet.reseau_actif].links[pivot].h + temps_correspondance))
                                                        {
                                                            if (projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd) * projet.param_affectation_horaire.cveh[succ_type] + (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[succ_type] + (temps_correspondance * projet.param_affectation_horaire.cboa[succ_type]) + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type] < cout2 && delta > -1)
                                                            {
                                                                cout2 = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd) * projet.param_affectation_horaire.cveh[succ_type] + (projet.reseaux[projet.reseau_actif].links[successeur].services[ii].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[ii].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[succ_type] + (temps_correspondance * projet.param_affectation_horaire.cboa[succ_type]) + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type];
                                                                num_service = ii;
                                                            }
                                                        }

                                                    }
                                                    if (num_service != -1)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].links[successeur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd) * projet.param_affectation_horaire.cveh[succ_type] + (projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[succ_type] + (temps_correspondance * projet.param_affectation_horaire.cboa[succ_type]) + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type])
                                                        {
                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Remove(successeur);
                                                            projet.reseaux[projet.reseau_actif].links[successeur].service = num_service;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd) * projet.param_affectation_horaire.cveh[succ_type] + (projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[num_service].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[succ_type] + (temps_correspondance * projet.param_affectation_horaire.cboa[succ_type]) + projet.reseaux[projet.reseau_actif].links[successeur].toll * projet.param_affectation_horaire.ctoll[succ_type];
                                                            projet.reseaux[projet.reseau_actif].links[successeur].touche = 2;

                                                            projet.reseaux[projet.reseau_actif].links[successeur].h = projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f;
                                                            if (projet.reseaux[projet.reseau_actif].links[pivot].ncorr == 0)
                                                            {
                                                                projet.reseaux[projet.reseau_actif].links[successeur].tatt1 = projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                            }
                                                            else
                                                            {
                                                                projet.reseaux[projet.reseau_actif].links[successeur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                            }
                                                            projet.reseaux[projet.reseau_actif].links[successeur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hd + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].delta * 1440f - projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh + projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hf - projet.reseaux[projet.reseau_actif].links[successeur].services[projet.reseaux[projet.reseau_actif].links[successeur].service].hd;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor + temps_correspondance;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr + 1;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[successeur].longueur;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[successeur].toll;

                                                            projet.reseaux[projet.reseau_actif].links[successeur].pivot = pivot;
                                                            projet.reseaux[projet.reseau_actif].links[successeur].turn_pivot = j;
                                                            if (projet.reseaux[projet.reseau_actif].links[pivot].pole == depart)
                                                            {
                                                                projet.reseaux[projet.reseau_actif].links[successeur].pole = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[successeur].no].i;
                                                            }
                                                            else
                                                            {
                                                                projet.reseaux[projet.reseau_actif].links[successeur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                                            }

                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[successeur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Add(successeur);
                                                            projet.param_affectation_horaire.nb_pop++;
                                                        }
                                                    }
                                                }


                                            }
                                        }
                                    }
                                    //projet.reseaux[projet.reseau_actif].links[pivot].touche = 3;
                                    //Console.WriteLine((touches.Count+calcules.Count).ToString());
                                }
                            fin_gga:
                                //Console.WriteLine(p.ToString());

                                int arrivee = -1;
                                double cout_fin = 1e38f;
                                if (projet.reseaux[projet.reseau_actif].numnoeud.TryGetValue(q, out value) == true)
                                {
                                    for (j = 0; j < projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].numnoeud[q]].pred.Count; j++)
                                    {
                                        int predecesseur = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].numnoeud[q]].pred[j];
                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].touche != 0 && projet.reseaux[projet.reseau_actif].links[predecesseur].cout < cout_fin)
                                        {
                                            arrivee = predecesseur;
                                            cout_fin = projet.reseaux[projet.reseau_actif].links[predecesseur].cout;

                                        }




                                    }
                                }
                                else
                                {
                                    fich_log.WriteLine("OD error" + libod + ":" + chaine + ": non existing destination node!");
                                }



                                if (arrivee != -1)
                                {
                                    if (projet.reseaux[projet.reseau_actif].links[arrivee].ligne > 0)
                                    {
                                        projet.reseaux[projet.reseau_actif].links[arrivee].alij += od;
                                        projet.reseaux[projet.reseau_actif].links[arrivee].services[projet.reseaux[projet.reseau_actif].links[arrivee].service].alij = od;
                                        projet.reseaux[projet.reseau_actif].links[arrivee].services[projet.reseaux[projet.reseau_actif].links[arrivee].service].alit += od;
                                    }
                                }
                                else
                                {
                                    fich_log.WriteLine("OD error" + libod + ":" + chaine + ": unreachable destination!");
                                }

                                pivot = arrivee;
                                string itineraire = "", texte;
                                if (pivot != -1)
                                {
                                    string[] param2 = { "|" }, lignes_corr = null;
                                    if (projet.reseaux[projet.reseau_actif].links[pivot].texte != null)
                                    {
                                        lignes_corr = projet.reseaux[projet.reseau_actif].links[pivot].texte.Split(param2, StringSplitOptions.RemoveEmptyEntries);
                                    }
                                    if (lignes_corr == null)
                                    {
                                        itineraire = "MAP";
                                    }
                                    else
                                    {
                                        itineraire = lignes_corr[0];
                                    }
                                }
                                while (pivot != -1)
                                {
                                    projet.reseaux[projet.reseau_actif].links[pivot].volau += od;
                                    if (projet.reseaux[projet.reseau_actif].links[pivot].pivot != -1 && projet.param_affectation_horaire.sortie_turns == true)
                                    {
                                        Turn virage = new Turn();
                                        virage.arci = projet.reseaux[projet.reseau_actif].links[pivot].pivot;
                                        virage.arcj = pivot;
                                        float value2;
                                        if (transfers.TryGetValue(virage, out value2) == true)
                                        {

                                            transfers[virage] += od;
                                        }
                                        else
                                        {
                                            transfers[virage] = od;
                                        }

                                        //projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].arcj[projet.reseaux[projet.reseau_actif].links[pivot].turn_pivot].volau += od;
                                    }
                                    if (projet.reseaux[projet.reseau_actif].links[pivot].service >= 0)
                                    {
                                        projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].volau += od;
                                    }

                                    if (projet.reseaux[projet.reseau_actif].links[pivot].pivot == -1)
                                    {
                                        if (projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0)
                                        {
                                            projet.reseaux[projet.reseau_actif].links[pivot].boai += od;
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].boai = od;
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].boat += od;

                                        }
                                    }
                                    else if (projet.reseaux[projet.reseau_actif].links[pivot].ligne != projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].ligne)
                                    {
                                        if (projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0)
                                        {
                                            projet.reseaux[projet.reseau_actif].links[pivot].boai += od;
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].boai = od;
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].boat += od;
                                        }
                                        if (projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].ligne > 0)
                                        {
                                            projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].alij += od;
                                            projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].services[projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].service].alij = od;
                                            projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].services[projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].service].alit += od;
                                        }

                                    }
                                    if (projet.param_affectation_horaire.sortie_chemins == true)
                                    {
                                        texte = libod + ";" + p + ";" + q + ";" + jour.ToString("0") + ";" + horaire.ToString("0.000");

                                        texte += ";" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[pivot].no].i;
                                        texte += ";" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[pivot].nd].i;
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].ligne.ToString("0");
                                        if (projet.reseaux[projet.reseau_actif].links[pivot].service >= 0)
                                        {
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].numero.ToString("0");
                                        }
                                        else
                                        {
                                            texte += ";-1";
                                        }
                                        texte += ";" + (projet.reseaux[projet.reseau_actif].links[pivot].h - horaire).ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].h.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].tveh.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].tmap.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].tatt.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].tcor.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].ncorr.ToString("0");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].tatt1.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].cout.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].l.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                        texte += ";" + od.ToString("0.00");
                                        if (projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0)
                                        {
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].boai.ToString("0.000");
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].alij.ToString("0.000");
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].boai = 0;
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].alij = 0;

                                        }
                                        else
                                        {
                                            texte += ";0.000";
                                            texte += ";0.000";
                                        }

                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].texte;
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].type;

                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].ttoll.ToString("0.000");

                                        fich_sortie2.WriteLine(texte);


                                    }
                                    if (projet.reseaux[projet.reseau_actif].links[pivot].pivot != -1)
                                    {
                                        if (projet.reseaux[projet.reseau_actif].links[pivot].ligne != projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].ligne)
                                        {
                                            string[] param2 = { "|" }, lignes_corr = null;
                                            if (projet.reseaux[projet.reseau_actif].links[pivot].texte != null)
                                            {

                                                lignes_corr = projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].texte.Split(param2, StringSplitOptions.RemoveEmptyEntries);
                                            }
                                            if (lignes_corr == null)
                                            {
                                                itineraire = "MAP|" + itineraire; ;
                                            }
                                            else
                                            {
                                                itineraire = lignes_corr[0] + "|" + itineraire;
                                            }
                                        }
                                    }
                                    pivot = projet.reseaux[projet.reseau_actif].links[pivot].pivot;
                                }
                                //fich_sortie.WriteLine("o;i;j;jour;heureo;heured;temps;tveh;tmap;tcorr;cout;volau;texte" );
                                if (arrivee != -1)
                                {
                                    texte = libod + ";" + p + ";" + q;
                                    texte += ";" + jour.ToString("0.000");
                                    texte += ";" + horaire.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].h.ToString("0.000");
                                    texte += ";" + (-horaire + projet.reseaux[projet.reseau_actif].links[arrivee].h).ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tveh.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tmap.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tatt.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tcor.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].ncorr.ToString("0");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tatt1.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].cout.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].l.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].pole;
                                    texte += ";" + od.ToString("0.00");
                                    //                                texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].texte;
                                    //itineraire = "MAP," + itineraire;

                                    texte += ";" + itineraire;
                                    texte += ";" + projet.param_affectation_horaire.nb_pop;
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].ttoll.ToString("0.000");


                                    fich_od.WriteLine(texte);

                                    if (projet.param_affectation_horaire.sortie_noeuds == true)
                                    {
                                        foreach (node n in projet.reseaux[projet.reseau_actif].nodes)
                                        {
                                            float tmax = 1e38f;
                                            int which_tmax = -1;
                                            String type_arc="" ;
                                            link troncon = new link();
                                            for (int s = 0; s < n.pred.Count; s++)
                                            {
                                                troncon = projet.reseaux[projet.reseau_actif].links[n.pred[s]];
                                                if (troncon.cout <= tmax && troncon.touche != 0 && (troncon.ligne <= 0 || projet.param_affectation_horaire.sortie_temps == 2))
                                                {
                                                    tmax = troncon.cout;
                                                    which_tmax = n.pred[s];
                                                    type_arc = troncon.type;
                                                }

                                            }
                                            if (which_tmax > 0 && tmax <= projet.param_affectation_horaire.temps_max)
                                            {
                                                if (filtre.Contains(type_arc) || filtre.Count == 0)
                                                {
                                                    texte = libod + ";" + p + ";" + q;
                                                    texte += ";" + jour.ToString("0.000");
                                                    texte += ";" + n.i;
                                                    texte += ";" + horaire.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].h.ToString("0.000");
                                                    texte += ";" + (-horaire + projet.reseaux[projet.reseau_actif].links[which_tmax].h).ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].tveh.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].tmap.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].tatt.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].tcor.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].ncorr.ToString("0");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].tatt1.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].cout.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].l.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].pole;
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].ttoll.ToString("0.000");

                                                    fich_noeuds.WriteLine(texte);
                                                }
                                            }
                                        }
                                    }

                                    if (projet.param_affectation_horaire.sortie_temps == 0)
                                    {
                                        network reseau = projet.reseaux[projet.reseau_actif];
                                        double som_detour = 0; double nb_detour = 0; double som_oiseau = 0;
                                        double d_oiseau, d_link;
                                        foreach (link li in reseau.links)
                                        {
                                            d_oiseau = Math.Pow(Math.Pow((reseau.nodes[reseau.numnoeud[p]].x - reseau.nodes[li.nd].x), 2) + Math.Pow((reseau.nodes[reseau.numnoeud[p]].y - reseau.nodes[li.nd].y), 2), 0.5);
                                            d_link = Math.Pow(Math.Pow((reseau.nodes[li.no].x - reseau.nodes[li.nd].x), 2) + Math.Pow((reseau.nodes[li.no].y - reseau.nodes[li.nd].y), 2), 0.5);

                                            if (d_oiseau > 500 & d_oiseau - d_link <= 500)
                                            {

                                                if (reseau.nodes[reseau.numnoeud[p]].x > 0 && reseau.nodes[reseau.numnoeud[p]].y > 0 && reseau.nodes[li.nd].x > 0 && reseau.nodes[li.nd].y > 0)
                                                {
                                                    if (li.h > 0)
                                                    {
                                                        som_detour += li.h;
                                                        som_oiseau += Math.Pow(Math.Pow((reseau.nodes[reseau.numnoeud[p]].x - reseau.nodes[li.nd].x), 2) + Math.Pow((reseau.nodes[reseau.numnoeud[p]].y - reseau.nodes[li.nd].y), 2), 0.5);
                                                        nb_detour++;
                                                    }
                                                }
                                            }
                                        }
                                        fich_detour.WriteLine(p + ";" + som_detour.ToString() + ";" + som_oiseau.ToString() + ";" + nb_detour.ToString());

                                    }

                                    if (projet.param_affectation_horaire.sortie_temps > 0)
                                    {
                                        for (i = 0; i < projet.reseaux[projet.reseau_actif].links.Count; i++)
                                        {
                                            arrivee = i;


                                            if (filtre.Contains(projet.reseaux[projet.reseau_actif].links[arrivee].type) || filtre.Count == 0)
                                            {
                                                if (projet.reseaux[projet.reseau_actif].links[arrivee].touche != 0 && (projet.reseaux[projet.reseau_actif].links[arrivee].ligne < 0 || projet.param_affectation_horaire.sortie_temps == 2))
                                                {
        
                                                    texte = libod + ";" + p;
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[arrivee].no].i;
                                                    texte += "-" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[arrivee].nd].i;
                                                    texte += ";" + (projet.reseaux[projet.reseau_actif].links[arrivee].ligne).ToString("0");
                                                    texte += ";" + i.ToString("0");
                                                    texte += ";" + jour.ToString("0");
                                                    texte += ";" + horaire.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].h.ToString("0.000");
                                                    texte += ";" + (-horaire + projet.reseaux[projet.reseau_actif].links[arrivee].h).ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tveh.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tmap.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tatt.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tcor.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].ncorr.ToString("0");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tatt1.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].cout.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].l.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].pole;
                                                    texte += ";" + od.ToString("0.00");
                                                    // texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].texte;
                                                    /*texte += ";" + projet.param_affectation_horaire.texte_cveh;
                                                    texte += ";" + projet.param_affectation_horaire.texte_cwait;
                                                    texte += ";" + projet.param_affectation_horaire.texte_cmap;
                                                    texte += ";" + projet.param_affectation_horaire.texte_cboa;
                                                    texte += ";" + projet.param_affectation_horaire.texte_coef_tmap;
                                                    texte += ";" + projet.param_affectation_horaire.texte_tboa;
                                                    texte += ";" + projet.param_affectation_horaire.nb_jours;*/
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].pivot.ToString("0");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].type;
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].ttoll.ToString("0.000");
                                                    link arc = new link();
                                                    arc = projet.reseaux[projet.reseau_actif].links[arrivee];
                                                    float ti;
                                                    if (arc.ligne < 0)
                                                    {
                                                        ti = -horaire + (arc.h - arc.temps * projet.param_affectation_horaire.coef_tmap[arc.type]);

                                                        //ti = -horaire + arc.h - arc.temps;
                                                    }
                                                    else
                                                    {
                                                        ti = -horaire + arc.h - (arc.services[arc.service].hf - arc.services[arc.service].hd);
                                                    }
                                                    texte += ";" + ti.ToString("0.000");


                                                    //                                itineraire = "MAP," + itineraire;
                                                    //texte += ";" + itineraire;
                                                    if ((projet.reseaux[projet.reseau_actif].links[arrivee].cout) <= projet.param_affectation_horaire.temps_max)
                                                    {

                                                        if (test_temps_per_min_depart(projet, arrivee) == true)
                                                        {
                                                            fich_sortie.WriteLine(texte);
                                                        }
                                                    }
                                                }
                                                else if (projet.reseaux[projet.reseau_actif].links[arrivee].touche == 0 && projet.param_affectation_horaire.sortie_isoles == true)
                                                {
                                                    texte = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[arrivee].no].i;
                                                    texte += "-" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[arrivee].nd].i;
                                                    texte += ";" + (projet.reseaux[projet.reseau_actif].links[arrivee].ligne).ToString("0");
                                                    texte += ";" + i.ToString("0");
                                                    fich_isoles.WriteLine(texte);

                                                }

                                            }
                                        }
                                    }
                                }
                            }

                            // sens heure d'arrivée
                            // sens heure d'arrivée
                            // sens heure d'arrivée
                            // sens heure d'arrivée
                            // sens heure d'arrivée
                            // sens heure d'arrivée
                            // sens heure d'arrivée
                            if (sens == 2)
                            {
                                if (q1 == q && jour1 == jour && horaire1 == horaire && sens1 == sens && ch.Length < 13)
                                {
                                    p1 = p;
                                    goto fin_gga2;
                                }
                                p1 = p; q1 = q; jour1 = jour; horaire1 = horaire; sens1 = sens;

                                for (i = 0; i < projet.reseaux[projet.reseau_actif].links.Count; i++)
                                {
                                    projet.reseaux[projet.reseau_actif].links[i].touche = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].cout = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].tatt = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].tatt1 = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].tcor = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].ncorr = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].tmap = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].tveh = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].h = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].ttoll = 0;
                                    projet.reseaux[projet.reseau_actif].links[i].l = 0;
                                    for (j = 0; j < projet.reseaux[projet.reseau_actif].links[i].services.Count; j++)
                                    {
                                        projet.reseaux[projet.reseau_actif].links[i].services[j].delta = 0;
                                        projet.reseaux[projet.reseau_actif].links[i].services[j].boai = 0;
                                        projet.reseaux[projet.reseau_actif].links[i].services[j].alij = 0;
                                    }
                                    projet.reseaux[projet.reseau_actif].links[i].pivot = -1;
                                    projet.reseaux[projet.reseau_actif].links[i].turn_pivot = -1;
                                    projet.reseaux[projet.reseau_actif].links[i].pole = "-1";
                                    projet.reseaux[projet.reseau_actif].links[i].service = -1;
                                    projet.reseaux[projet.reseau_actif].links[i].is_queue = false;



                                }
                                gga_nq.Clear();
                                string depart = q;
                                int pivot = -1, value;
                                int bucket, id_bucket = 0, predecesseur;
                                float penalite = 0, temps_correspondance, max_correspondance;
                                if (projet.reseaux[projet.reseau_actif].numnoeud.TryGetValue(depart, out value) == true)
                                {

                                    for (j = 0; j < projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].numnoeud[depart]].pred.Count; j++)
                                    {
                                        predecesseur = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].numnoeud[depart]].pred[j];
                                        String pred_type = projet.reseaux[projet.reseau_actif].links[predecesseur].type;
                                        max_correspondance = projet.param_affectation_horaire.tboa_max[pred_type];




                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].ligne < 0 && projet.param_affectation_horaire.cmap[pred_type] > 0 && projet.reseaux[projet.reseau_actif].links[predecesseur].temps < projet.param_affectation_horaire.tmapmax)
                                        {
                                            bool test_periode = false;

                                            if (projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count > 0)
                                            {
                                                int decal_jour = (int)Math.Floor(horaire / 1440f);
                                                for (int kk = 0; kk < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; kk++)
                                                {
                                                    if (Math.Abs(decal_jour) <= projet.param_affectation_horaire.nb_jours)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].regime].Substring(jour + decal_jour, 1) == "O" && projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].hd + 1440f * decal_jour <= horaire && projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].hf + 1440f * decal_jour > horaire)
                                                        {
                                                            test_periode = true;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].service = kk;
                                                        }
                                                    }
                                                }

                                            }
                                            else
                                            {
                                                test_periode = true;
                                            }

                                            if (test_periode == true)
                                            {


                                                //touches.Enqueue(successeur);
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 1;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].cout = (projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type] * projet.param_affectation_horaire.cmap[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = (projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type];
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                projet.reseaux[projet.reseau_actif].links[predecesseur].h = horaire - (projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type];
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = -1;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = -1;

                                                projet.reseaux[projet.reseau_actif].links[predecesseur].pole = depart;
                                                //                                    bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                while (bucket >= gga_nq.Count)
                                                {
                                                    gga_nq.Add(new List<int>());
                                                }
                                                gga_nq[bucket].Add(predecesseur);
                                                projet.param_affectation_horaire.nb_pop++;
                                            }
                                        }
                                        else if (projet.param_affectation_horaire.cveh[pred_type] > 0)
                                        {
                                            int ii, jj, num_service = -1, h3 = 0, delta, duree_periode;
                                            float h1 = 1e38f, h2 = 1e38f, cout2 = 1e38f;
                                            for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; ii++)
                                            {
                                                delta = 0;
                                                duree_periode = projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Length;

                                                if ((projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf > horaire) || projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Substring(jour, 1) == "N")
                                                {

                                                    h1 = -1e38f;
                                                    h2 = 1e38f;
                                                    h3 = -1;
                                                    for (jj = jour - 1; jj >= Math.Max(jour - projet.param_affectation_horaire.nb_jours, 0); jj--)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Substring(jj, 1) == "O" && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f) > h1 && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f) < horaire)
                                                        {
                                                            h1 = projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f;
                                                            h2 = (-jour + jj);
                                                            h3 = jj;
                                                        }

                                                    }
                                                    if (h3 != -1)
                                                    {
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta = h2;
                                                    }
                                                    else
                                                    {
                                                        delta = 1;
                                                    }


                                                }

                                                if (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 60f * 24f + horaire < max_correspondance)
                                                {
                                                    if (((projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 60f * 24f + horaire) * projet.param_affectation_horaire.cwait[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type]) < cout2 && delta < 1)
                                                    {
                                                        cout2 = (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 60f * 24f + horaire) * projet.param_affectation_horaire.cwait[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                        num_service = ii;

                                                    }
                                                }

                                            }
                                            if (num_service != -1)
                                            {
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].service = num_service;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].cout = (projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].delta * 1440f + horaire) * projet.param_affectation_horaire.cwait[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];

                                                projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 1;

                                                projet.reseaux[projet.reseau_actif].links[predecesseur].h = projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd + projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 60f * 24f;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tatt = -projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + horaire;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = -projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + horaire;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tveh = projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tcor = 0;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].ncorr = 1;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = 0;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                while (bucket >= gga_nq.Count)
                                                {
                                                    gga_nq.Add(new List<int>());
                                                }
                                                gga_nq[bucket].Add(predecesseur);
                                                projet.param_affectation_horaire.nb_pop++;
                                                //                                touches.Enqueue(successeur);
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = -1;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = -1;
                                                projet.reseaux[projet.reseau_actif].links[predecesseur].pole = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[predecesseur].nd].i;
                                            }
                                        }

                                    }
                                }
                                else
                                {
                                    fich_log.WriteLine("OD error" + libod + ":" + chaine + ": non existing destination node!");
                                }
                                int bucket_cout_max = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.param_affectation_horaire.temps_max / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));

                                while (gga_nq.Count > id_bucket &&  bucket_cout_max > id_bucket)
                                {

                                    while (gga_nq[id_bucket].Count == 0)
                                    {
                                        id_bucket++;
                                        if (id_bucket == gga_nq.Count || bucket_cout_max == id_bucket)
                                        {
                                            goto fin_gga2;
                                        }
                                    }
                                    if (projet.param_affectation_horaire.algorithme == 0)
                                    {
                                        pivot = gga_nq[id_bucket][0];
                                        gga_nq[id_bucket].RemoveAt(0);
                                        projet.reseaux[projet.reseau_actif].links[pivot].touche = 1;
                                    }
                                    else
                                    {
                                        int k, id_pivot = -1; double cout_max = 1e38f;
                                        for (k = 0; k < gga_nq[id_bucket].Count; k++)
                                        {
                                            if (projet.reseaux[projet.reseau_actif].links[gga_nq[id_bucket][k]].cout < cout_max)
                                            {
                                                cout_max = projet.reseaux[projet.reseau_actif].links[gga_nq[id_bucket][k]].cout;
                                                id_pivot = k;
                                            }
                                        }
                                        pivot = gga_nq[id_bucket][id_pivot];
                                        gga_nq[id_bucket].RemoveAt(id_pivot);
                                        projet.reseaux[projet.reseau_actif].links[pivot].touche = 3;
                                    }


                                    //avancement.textBox1.Text = touches.Count.ToString() + " " + calcules.Count.ToString() + " " + projet.reseaux[projet.reseau_actif].links[pivot].cout;
                                    //avancement.textBox1.Refresh();
                                    for (j = 0; j < projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[pivot].no].pred.Count; j++)
                                    {

                                        String pivot_type = projet.reseaux[projet.reseau_actif].links[pivot].type;
                                        link troncon_pred = projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[pivot].no].pred[j]];
                                        link troncon_pivot = projet.reseaux[projet.reseau_actif].links[pivot];
                                        predecesseur = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[pivot].no].pred[j];
                                        String pred_type = projet.reseaux[projet.reseau_actif].links[predecesseur].type;

                                        if (projet.param_affectation_horaire.demitours == true)
                                        {

                                            if (troncon_pivot.nd == troncon_pred.no)
                                            {
     
                                                penalite = -1;
                                            }
                                            else
                                            {
                                                penalite = 0;
                                            }
                                        }

                                        else
                                        {
                                            penalite = 0;
                                        }
                                        Turn virage = new Turn();
                                        virage.arci = predecesseur;
                                        virage.arcj = pivot;
                                        float value2;
                                        if (projet.reseaux[projet.reseau_actif].nodes[troncon_pivot.no].is_intersection == true)
                                        {
                                            if (turns.TryGetValue(virage, out value2) == true)
                                            {
                                                penalite = turns[virage];
                                                pred_type = projet.reseaux[projet.reseau_actif].links[predecesseur].type;
                                            }
                                            else
                                            {
                                                penalite = 0;
                                            }
                                        }



                                        if (penalite >= 0)
                                        {
                                            if (penalite > 0)
                                            {
                                                temps_correspondance = penalite;
                                                max_correspondance = projet.param_affectation_horaire.tboa_max[pivot_type];

                                            }
                                            else
                                            {
                                                temps_correspondance = projet.param_affectation_horaire.tboa[pivot_type];
                                                max_correspondance = projet.param_affectation_horaire.tboa_max[pivot_type];

                                            }
                                            //successeurs touches pour la première fois
                                            if (projet.reseaux[projet.reseau_actif].links[predecesseur].touche == 0)
                                            {
                                                // predecesseur marche à pied pivot marche
                                                if (projet.reseaux[projet.reseau_actif].links[predecesseur].ligne < 0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne < 0 && projet.param_affectation_horaire.cmap[pred_type] > 0 && (projet.reseaux[projet.reseau_actif].links[pivot].tmap + projet.reseaux[projet.reseau_actif].links[predecesseur].temps < projet.param_affectation_horaire.tmapmax))
                                                {
                                                    bool test_periode = false;
                                                    projet.reseaux[projet.reseau_actif].links[predecesseur].service = -1;
                                                    if (projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count > 0)
                                                    {
                                                        int decal_jour = (int)(Math.Floor((projet.reseaux[projet.reseau_actif].links[pivot].h - penalite) / 1440f));
                                                        for (int kk = 0; kk < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; kk++)
                                                        {
                                                            if (Math.Abs(decal_jour) <= projet.param_affectation_horaire.nb_jours)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].regime].Substring(jour + decal_jour, 1) == "O" && projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].hd + 1440f * decal_jour <= projet.reseaux[projet.reseau_actif].links[pivot].h - penalite && projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].hf + 1440f * decal_jour > projet.reseaux[projet.reseau_actif].links[pivot].h - penalite)
                                                                {
                                                                    test_periode = true;
                                                                    projet.reseaux[projet.reseau_actif].links[predecesseur].service = kk;
                                                                }
                                                            }
                                                        }

                                                    }
                                                    else
                                                    {
                                                        test_periode = true;
                                                    }

                                                    if (test_periode == true)
                                                    {

                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].temps + penalite) * projet.param_affectation_horaire.coef_tmap[pred_type] * projet.param_affectation_horaire.cmap[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].h = projet.reseaux[projet.reseau_actif].links[pivot].h - (projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type] - penalite;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap + (projet.reseaux[projet.reseau_actif].links[predecesseur].temps + penalite) * projet.param_affectation_horaire.coef_tmap[pred_type];
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 1;

                                                        //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                        bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                        while (bucket >= gga_nq.Count)
                                                        {
                                                            gga_nq.Add(new List<int>());
                                                        }
                                                        gga_nq[bucket].Add(predecesseur);
                                                        projet.param_affectation_horaire.nb_pop++;
                                                        //                                        touches.Enqueue(successeur);
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = pivot;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = j;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                                    }
                                                }
                                                // predecesseur marche à pied pivot TC
                                                else if (projet.reseaux[projet.reseau_actif].links[predecesseur].ligne < 0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0 && projet.param_affectation_horaire.cmap[pred_type] > 0 && (projet.reseaux[projet.reseau_actif].links[pivot].tmap + projet.reseaux[projet.reseau_actif].links[predecesseur].temps < projet.param_affectation_horaire.tmapmax))
                                                {
                                                    bool test_periode = false;
                                                    projet.reseaux[projet.reseau_actif].links[predecesseur].service = -1;


                                                    if (projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count > 0)
                                                    {
                                                        int decal_jour = -(int)(Math.Floor((projet.reseaux[projet.reseau_actif].links[pivot].h - temps_correspondance) / 1440f));
                                                        for (int kk = 0; kk < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; kk++)
                                                        {
                                                            if (decal_jour <= projet.param_affectation_horaire.nb_jours)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].regime].Substring(jour - decal_jour, 1) == "O" && projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].hd - 1440f * decal_jour <= projet.reseaux[projet.reseau_actif].links[pivot].h - temps_correspondance && projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].hf - 1440f * decal_jour > projet.reseaux[projet.reseau_actif].links[pivot].h - temps_correspondance)
                                                                {
                                                                    test_periode = true;
                                                                    projet.reseaux[projet.reseau_actif].links[predecesseur].service = kk;
                                                                }
                                                            }
                                                        }

                                                    }
                                                    else
                                                    {
                                                        test_periode = true;
                                                    }

                                                    if (test_periode == true)
                                                    {


                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].temps + penalite) * projet.param_affectation_horaire.coef_tmap[pred_type] * projet.param_affectation_horaire.cmap[pred_type] + projet.param_affectation_horaire.cboa[pivot_type] * temps_correspondance + temps_correspondance * projet.param_affectation_horaire.cwait[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].h = projet.reseaux[projet.reseau_actif].links[pivot].h - (projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type] - temps_correspondance - penalite;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt + temps_correspondance;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor + temps_correspondance;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr+1;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap + (projet.reseaux[projet.reseau_actif].links[predecesseur].temps + penalite) * projet.param_affectation_horaire.coef_tmap[pred_type];
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 1;
                                                        // bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                        bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                        while (bucket >= gga_nq.Count)
                                                        {
                                                            gga_nq.Add(new List<int>());
                                                        }
                                                        gga_nq[bucket].Add(predecesseur);
                                                        projet.param_affectation_horaire.nb_pop++;
                                                        //                                        touches.Enqueue(successeur);
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = pivot;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = j;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].pole = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[predecesseur].nd].i;
                                                    }
                                                }
                                                //predecesseurs TC même ligne
                                                else if (projet.reseaux[projet.reseau_actif].links[predecesseur].ligne == projet.reseaux[projet.reseau_actif].links[pivot].ligne && projet.reseaux[projet.reseau_actif].links[predecesseur].ligne > 0 && projet.param_affectation_horaire.cveh[pred_type] > 0)
                                                {
                                                    int ii, num_service = -1;
                                                    for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; ii++)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].numero == projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].numero)
                                                        {
                                                            if (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf <= projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].hd)
                                                            {
                                                                num_service = ii;
                                                            }
                                                        }
                                                    }
                                                    if (num_service != -1 && projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf + projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].delta * 1440f <= projet.reseaux[projet.reseau_actif].links[pivot].h)
                                                    {
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].service = num_service;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].delta = projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].delta;

                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 1;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cveh[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].h = projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd + projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 60f * 24f;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                        //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                        bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                        while (bucket >= gga_nq.Count)
                                                        {
                                                            gga_nq.Add(new List<int>());
                                                        }
                                                        gga_nq[bucket].Add(predecesseur);
                                                        projet.param_affectation_horaire.nb_pop++;
                                                        //touches.Enqueue(successeur);
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = pivot;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = j;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                                    }
                                                }

                                                //predecesseur TC lignes différentes
                                                else if (projet.reseaux[projet.reseau_actif].links[predecesseur].ligne != projet.reseaux[projet.reseau_actif].links[pivot].ligne && projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0 && projet.reseaux[projet.reseau_actif].links[predecesseur].ligne > 0 && projet.param_affectation_horaire.cveh[pred_type] > 0)
                                                {
                                                    int ii, jj, num_service = -1, h3 = 0, delta, duree_periode;
                                                    float h1 = -1e38f, h2 = 1e38f, cout2 = 1e38f;
                                                    for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; ii++)
                                                    {
                                                        delta = 0;
                                                        duree_periode = projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Length;

                                                        if ((projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + temps_correspondance > projet.reseaux[projet.reseau_actif].links[pivot].h) || projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Substring(jour, 1) == "N")
                                                        {

                                                            h1 = -1e38f;
                                                            h2 = 1e38f;
                                                            h3 = -1;
                                                            for (jj = jour - 1; jj >= Math.Max(jour - projet.param_affectation_horaire.nb_jours, 0); jj--)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Substring(jj, 1) == "O" && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f) > h1 && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f) + temps_correspondance < projet.reseaux[projet.reseau_actif].links[pivot].h)
                                                                {
                                                                    h1 = projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f;
                                                                    h2 = (-jour + jj);
                                                                    h3 = jj;
                                                                }

                                                            }
                                                            if (h3 != -1)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta > h2 || projet.reseaux[projet.reseau_actif].links[predecesseur].touche == 0)
                                                                {
                                                                    projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta = h2;
                                                                }
                                                            }
                                                            else
                                                            {
                                                                delta = 1;
                                                            }


                                                        }
                                                        if ((projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 1440f + max_correspondance > projet.reseaux[projet.reseau_actif].links[pivot].h) && ( projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 1440f + temps_correspondance <= projet.reseaux[projet.reseau_actif].links[pivot].h))
                                                        {
                                                            if ((projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 60f * 24f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + temps_correspondance * projet.param_affectation_horaire.cboa[pivot_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type]) < cout2 && delta < 1)
                                                            {

                                                                cout2 = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 60f * 24f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + temps_correspondance * projet.param_affectation_horaire.cboa[pivot_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                                num_service = ii;

                                                            }
                                                        }

                                                    }
                                                    if (num_service != -1)
                                                    {
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].service = num_service;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pivot_type] + (temps_correspondance * projet.param_affectation_horaire.cboa[pivot_type]) + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];

                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 1;

                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].h = projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd + projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 60f * 24f;
                                                        if (projet.reseaux[projet.reseau_actif].links[pivot].ncorr == 0)
                                                        {
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = -projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                        }
                                                        else
                                                        {
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                        }

                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh + projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor + temps_correspondance;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr + 1;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                        //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                        bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                        while (bucket >= gga_nq.Count)
                                                        {
                                                            gga_nq.Add(new List<int>());
                                                        }
                                                        gga_nq[bucket].Add(predecesseur);
                                                        projet.param_affectation_horaire.nb_pop++;
                                                        //                                        touches.Enqueue(successeur);
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = pivot;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = j;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].pole = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[predecesseur].nd].i;
                                                    }
                                                }

                                                //predecesseur TC lignes différentes pivot MAP
                                                else if (projet.reseaux[projet.reseau_actif].links[predecesseur].ligne > 0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne < 0 && projet.param_affectation_horaire.cveh[pred_type] > 0)
                                                {
                                                    int ii, jj, num_service = -1, h3 = 0, delta, duree_periode;
                                                    float h1 = 1e38f, h2 = 1e38f, cout2 = 1e38f;
                                                    for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; ii++)
                                                    {
                                                        delta = 0;
                                                        duree_periode = projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Length;
                                                        if ((projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf > projet.reseaux[projet.reseau_actif].links[pivot].h) || projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Substring(jour, 1) == "N")
                                                        {
                                                            h1 = -1e38f;
                                                            h2 = 1e38f;
                                                            h3 = -1;

                                                            for (jj = jour - 1; jj >= Math.Max(jour - projet.param_affectation_horaire.nb_jours, 0); jj--)
                                                            {

                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Substring(jj, 1) == "O" && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f) > h1 && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f) < projet.reseaux[projet.reseau_actif].links[pivot].h)
                                                                {
                                                                    h1 = projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f;
                                                                    h2 = (-jour + jj);
                                                                    h3 = jj;
                                                                }

                                                            }
                                                            if (h3 != -1)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta > h2 || projet.reseaux[projet.reseau_actif].links[predecesseur].touche == 0)
                                                                {
                                                                    projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta = h2;
                                                                }
                                                            }
                                                            else
                                                            {
                                                                delta = 1;
                                                            }


                                                        }
                                                        if ( (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 1440f  <= projet.reseaux[projet.reseau_actif].links[pivot].h))

                                                        {
                                                            if ((projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 60f * 24f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type]) + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type] < cout2 && delta < 1)
                                                            {
                                                                cout2 = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 60f * 24f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                                num_service = ii;

                                                            }
                                                        }

                                                    }
                                                    if (num_service != -1)
                                                    {
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].service = num_service;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];

                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 1;

                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].h = projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd + projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 24f * 60f;
                                                        if (projet.reseaux[projet.reseau_actif].links[pivot].ncorr == 0)
                                                        {
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = -projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                        }
                                                        else
                                                        {
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;

                                                        }
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh + projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;                                                //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                        bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                        while (bucket >= gga_nq.Count)
                                                        {
                                                            gga_nq.Add(new List<int>());
                                                        }
                                                        gga_nq[bucket].Add(predecesseur);
                                                        projet.param_affectation_horaire.nb_pop++;
                                                        //                                        touches.Enqueue(successeur);
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = pivot;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = j;
                                                        projet.reseaux[projet.reseau_actif].links[predecesseur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                                    }
                                                }

                                            }


                                            //eléments déjà touchés
                                            else if (projet.reseaux[projet.reseau_actif].links[predecesseur].touche == 1 || projet.reseaux[projet.reseau_actif].links[predecesseur].touche == 2)
                                            {
                                                //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                              
                                                
                                     //successeurs marche à pied pivot MAP

                                                if (projet.reseaux[projet.reseau_actif].links[predecesseur].ligne < 0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne < 0 && projet.param_affectation_horaire.cmap[pred_type] > 0 && (projet.reseaux[projet.reseau_actif].links[pivot].tmap + projet.reseaux[projet.reseau_actif].links[predecesseur].temps < projet.param_affectation_horaire.tmapmax) && projet.reseaux[projet.reseau_actif].links[predecesseur].cout>projet.reseaux[projet.reseau_actif].links[pivot].cout)
                                                {
                                                    bool test_periode = false;
                                                    int id_service = -1;
                                                    if (projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count > 0)
                                                    {
                                                        int decal_jour = (int)(Math.Floor((projet.reseaux[projet.reseau_actif].links[pivot].h - penalite) / 1440f));
                                                        for (int kk = 0; kk < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; kk++)
                                                        {
                                                            if (Math.Abs(decal_jour) <= projet.param_affectation_horaire.nb_jours)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].regime].Substring(jour + decal_jour, 1) == "O" && projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].hd + 1440f * decal_jour <= projet.reseaux[projet.reseau_actif].links[pivot].h - penalite && projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].hf + 1440f * decal_jour > projet.reseaux[projet.reseau_actif].links[pivot].h - penalite)
                                                                {
                                                                    test_periode = true;
                                                                    id_service = kk;
                                                                }
                                                            }
                                                        }

                                                    }
                                                    else
                                                    {
                                                        test_periode = true;
                                                    }

                                                    if (test_periode == true)
                                                    {


                                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout + (penalite + projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type] * projet.param_affectation_horaire.cmap[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type])
                                                        {

                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Remove(predecesseur);
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (penalite + projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type] * projet.param_affectation_horaire.cmap[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].h = projet.reseaux[projet.reseau_actif].links[pivot].h - (projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type] - penalite;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap + (penalite + projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type];
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 2;

                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = pivot;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = j;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].service = id_service;

                                                            //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Add(predecesseur);
                                                            projet.param_affectation_horaire.nb_pop++;

                                                        }
                                                    }

                                                }
                                                //predecesseurs marche à pied pivot TC
                                                else if (projet.reseaux[projet.reseau_actif].links[predecesseur].ligne < 0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0 && projet.param_affectation_horaire.cmap[pred_type] > 0 && (projet.reseaux[projet.reseau_actif].links[pivot].tmap + projet.reseaux[projet.reseau_actif].links[predecesseur].temps < projet.param_affectation_horaire.tmapmax) && projet.reseaux[projet.reseau_actif].links[predecesseur].cout> projet.reseaux[projet.reseau_actif].links[pivot].cout)
                                                {
                                                    int id_service = -1;
                                                    bool test_periode = false;

                                                    if (projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count > 0)
                                                    {
                                                        int decal_jour = -(int)(Math.Floor((projet.reseaux[projet.reseau_actif].links[pivot].h - temps_correspondance) / 1440f));
                                                        for (int kk = 0; kk < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; kk++)
                                                        {
                                                            if (decal_jour <= projet.param_affectation_horaire.nb_jours)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].regime].Substring(jour - decal_jour, 1) == "O" && projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].hd - 1440f * decal_jour <= projet.reseaux[projet.reseau_actif].links[pivot].h - penalite - temps_correspondance && projet.reseaux[projet.reseau_actif].links[predecesseur].services[kk].hf - 1440f * decal_jour > projet.reseaux[projet.reseau_actif].links[pivot].h - penalite - temps_correspondance)
                                                                {
                                                                    test_periode = true;
                                                                    id_service = kk;

                                                                }
                                                            }
                                                        }

                                                    }
                                                    else
                                                    {
                                                        test_periode = true;
                                                    }

                                                    if (test_periode == true)
                                                    {


                                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout + (penalite + projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type] * projet.param_affectation_horaire.cmap[pred_type] + projet.param_affectation_horaire.cboa[pivot_type] * temps_correspondance + projet.param_affectation_horaire.cwait[pred_type] * temps_correspondance + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type])
                                                        {
                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Remove(predecesseur);
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (penalite + projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type] * projet.param_affectation_horaire.cmap[pred_type] + projet.param_affectation_horaire.cboa[pivot_type] * temps_correspondance + projet.param_affectation_horaire.cwait[pred_type] * temps_correspondance + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].h = projet.reseaux[projet.reseau_actif].links[pivot].h - (projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type] - temps_correspondance - penalite;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt + temps_correspondance;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor + temps_correspondance;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr+1;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap + (penalite + projet.reseaux[projet.reseau_actif].links[predecesseur].temps) * projet.param_affectation_horaire.coef_tmap[pred_type];
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 2;

                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = pivot;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].pole = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[predecesseur].nd].i;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = j;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].service = id_service;
                                                            //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Add(predecesseur);
                                                            projet.param_affectation_horaire.nb_pop++;

                                                        }
                                                    }

                                                }
                                                //successeurs TC même ligne
                                                else if ((projet.reseaux[projet.reseau_actif].links[predecesseur].ligne == projet.reseaux[projet.reseau_actif].links[pivot].ligne && projet.param_affectation_horaire.cveh[pred_type] > 0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0) && (projet.reseaux[projet.reseau_actif].links[predecesseur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout))
                                                {
                                                    int ii, num_service = -1;
                                                    for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; ii++)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].numero == projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].numero)
                                                        {
                                                            if (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf <= projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].hd)
                                                            {
                                                                num_service = ii;
                                                            }
                                                        }


                                                    }

                                                    if (num_service != -1)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf + projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].delta * 1440f <= projet.reseaux[projet.reseau_actif].links[pivot].h)
                                                        {

                                                            if (projet.reseaux[projet.reseau_actif].links[predecesseur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hd - projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cveh[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type] && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf <= projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].hd))
                                                            {
                                                                bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                                gga_nq[bucket].Remove(predecesseur);
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].service = num_service;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].delta = projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].delta;

                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 2;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cveh[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].h = projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd + projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 60f * 24f;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd /*- projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f*/ + projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = pivot;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = j;
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                                                //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                                bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                                gga_nq[bucket].Add(predecesseur);
                                                                projet.param_affectation_horaire.nb_pop++;
                                                            }
                                                        }
                                                    }
                                                }
                                                //successeurs TC lignes différentes
                                                else if ((projet.reseaux[projet.reseau_actif].links[predecesseur].ligne != projet.reseaux[projet.reseau_actif].links[pivot].ligne && projet.param_affectation_horaire.cveh[pred_type] > 0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0 && projet.reseaux[projet.reseau_actif].links[predecesseur].ligne > 0) && (projet.reseaux[projet.reseau_actif].links[predecesseur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout))
                                                {
                                                    int ii, jj, num_service = -1, h3 = -1, delta, duree_periode;
                                                    float h1 = 1e38f, h2 = 1e38f, cout2 = 1e38f;
                                                    for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; ii++)
                                                    {
                                                        delta = 0;
                                                        duree_periode = projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Length;

                                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + temps_correspondance > projet.reseaux[projet.reseau_actif].links[pivot].h || projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Substring(jour, 1) == "N")
                                                        {

                                                            h1 = -1e38f;
                                                            h2 = 1e38f;
                                                            h3 = -1;
                                                            for (jj = jour - 1; jj >= Math.Max(jour - projet.param_affectation_horaire.nb_jours, 0); jj--)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Substring(jj, 1) == "O" && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f) > h1 && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f) + temps_correspondance < projet.reseaux[projet.reseau_actif].links[pivot].h)
                                                                {
                                                                    h1 = projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f;
                                                                    h2 = (-jour + jj);
                                                                    h3 = jj;
                                                                }

                                                            }
                                                            if (h3 != -1)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta > h2 || projet.reseaux[projet.reseau_actif].links[predecesseur].touche == 0)
                                                                {
                                                                    projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta = h2;
                                                                }

                                                            }
                                                            else
                                                            {
                                                                delta = 1;
                                                            }


                                                        }
                                                        if ((projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 1440f + max_correspondance > projet.reseaux[projet.reseau_actif].links[pivot].h) && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 1440f + temps_correspondance <= projet.reseaux[projet.reseau_actif].links[pivot].h))

                                                        {
                                                            if (projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 60f * 24f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + (temps_correspondance * projet.param_affectation_horaire.cboa[pivot_type]) + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type] < cout2 && delta < 1)
                                                            {
                                                                cout2 = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 60f * 24f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + (temps_correspondance * projet.param_affectation_horaire.cboa[pivot_type]) + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                                num_service = ii;
                                                            }
                                                        }

                                                    }

                                                    if (num_service != -1)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + (temps_correspondance * projet.param_affectation_horaire.cboa[pivot_type]) + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type])
                                                        {
                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Remove(predecesseur);
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].service = num_service;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + (temps_correspondance * projet.param_affectation_horaire.cboa[pivot_type]) + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 2;

                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].h = projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd + projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 60f * 24f;
                                                            if (projet.reseaux[projet.reseau_actif].links[pivot].tatt1 == 0)
                                                            {
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = -projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                            }
                                                            else
                                                            {
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;

                                                            }
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh + projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor + temps_correspondance;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr + 1;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = pivot;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = j;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].pole = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[predecesseur].nd].i;
                                                            //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Add(predecesseur);
                                                            projet.param_affectation_horaire.nb_pop++;
                                                        }
                                                    }

                                                }
                                                //predecesseurs TC lignes différentes pivot MAP
                                                else if ((projet.reseaux[projet.reseau_actif].links[predecesseur].ligne > 0 && projet.reseaux[projet.reseau_actif].links[predecesseur].ligne!= projet.reseaux[projet.reseau_actif].links[pivot].ligne && projet.param_affectation_horaire.cveh[pred_type] > 0 && projet.reseaux[projet.reseau_actif].links[pivot].ligne < 0) && (projet.reseaux[projet.reseau_actif].links[predecesseur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout))
                                                {
                                                    int ii, jj, num_service = -1, h3 = -1, delta, duree_periode;
                                                    float h1 = 1e38f, h2 = 1e38f, cout2 = 1e38f;
                                                    for (ii = 0; ii < projet.reseaux[projet.reseau_actif].links[predecesseur].services.Count; ii++)
                                                    {
                                                        delta = 0;

                                                        duree_periode = projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Length;

                                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf > projet.reseaux[projet.reseau_actif].links[pivot].h || projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Substring(jour, 1) == "N")
                                                        {

                                                            h1 = -1e38f;
                                                            h2 = 1e38f;
                                                            h3 = -1;
                                                            for (jj = jour - 1; jj >= Math.Max(jour - projet.param_affectation_horaire.nb_jours, 0); jj--)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].regime].Substring(jj, 1) == "O" && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f) > h1 && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f) < projet.reseaux[projet.reseau_actif].links[pivot].h)
                                                                {
                                                                    h1 = projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + (-jour + jj) * 24f * 60f;
                                                                    h2 = (-jour + jj);
                                                                    h3 = jj;
                                                                }

                                                            }
                                                            if (h3 != -1)
                                                            {
                                                                if (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta > h2 || projet.reseaux[projet.reseau_actif].links[predecesseur].touche == 0)
                                                                {
                                                                    projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta = h2;
                                                                }
                                                            }
                                                            else
                                                            {
                                                                delta = 1;
                                                            }


                                                        }
                                                        if ((projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 1440f + max_correspondance > projet.reseaux[projet.reseau_actif].links[pivot].h) && (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf + projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 1440f + temps_correspondance <= projet.reseaux[projet.reseau_actif].links[pivot].h))

                                                        {
                                                            if (projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 60f * 24f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type] < cout2 && delta < 1)
                                                            {
                                                                num_service = ii;
                                                                cout2 = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[ii].delta * 60f * 24f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                            }
                                                        }
                                                    }

                                                    if (num_service != -1)
                                                    {
                                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].cout > projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type])
                                                        {

                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Remove(predecesseur);
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].service = num_service;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].cout = projet.reseaux[projet.reseau_actif].links[pivot].cout + (projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hd) * projet.param_affectation_horaire.cveh[pred_type] + (-projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[num_service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h) * projet.param_affectation_horaire.cwait[pred_type] + projet.reseaux[projet.reseau_actif].links[predecesseur].toll * projet.param_affectation_horaire.ctoll[pred_type];
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].touche = 2;

                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].h = projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd + projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 60f * 24f;
                                                            if (projet.reseaux[projet.reseau_actif].links[pivot].tatt1 == 0)
                                                            {
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = -projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                            }
                                                            else
                                                            {
                                                                projet.reseaux[projet.reseau_actif].links[predecesseur].tatt1 = projet.reseaux[projet.reseau_actif].links[pivot].tatt1;

                                                            }
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tatt = projet.reseaux[projet.reseau_actif].links[pivot].tatt - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].delta * 1440f + projet.reseaux[projet.reseau_actif].links[pivot].h;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tveh = projet.reseaux[projet.reseau_actif].links[pivot].tveh + projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hf - projet.reseaux[projet.reseau_actif].links[predecesseur].services[projet.reseaux[projet.reseau_actif].links[predecesseur].service].hd;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tcor = projet.reseaux[projet.reseau_actif].links[pivot].tcor+temps_correspondance;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].ncorr = projet.reseaux[projet.reseau_actif].links[pivot].ncorr + 1;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].tmap = projet.reseaux[projet.reseau_actif].links[pivot].tmap;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].ttoll = projet.reseaux[projet.reseau_actif].links[pivot].ttoll + projet.reseaux[projet.reseau_actif].links[predecesseur].toll;

                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].l = projet.reseaux[projet.reseau_actif].links[pivot].l + projet.reseaux[projet.reseau_actif].links[predecesseur].longueur;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].pivot = pivot;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].turn_pivot = j;
                                                            projet.reseaux[projet.reseau_actif].links[predecesseur].pole = projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                                            //bucket = (int)Math.Truncate(Math.Min((Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout, 2) / projet.param_affectation_horaire.param_dijkstra), projet.param_affectation_horaire.max_nb_buckets));
                                                            bucket = Convert.ToInt32(Math.Truncate(Math.Min(Math.Pow(projet.reseaux[projet.reseau_actif].links[predecesseur].cout / projet.param_affectation_horaire.param_dijkstra, projet.param_affectation_horaire.pu), projet.param_affectation_horaire.max_nb_buckets)));
                                                            gga_nq[bucket].Add(predecesseur);
                                                            projet.param_affectation_horaire.nb_pop++;
                                                        }
                                                    }
                                                }


                                            }

                                            List<int> liste = new List<int>();
                                            liste.Add(1289714);
                                            liste.Add(233502);
                                            liste.Add(233499);
                                            liste.Add(1289712);

                                            if (liste.Contains(pivot) || liste.Contains(predecesseur))
                                                {
                                                String texto = "pivot:" + projet.reseaux[projet.reseau_actif].links[pivot].no.ToString() + " " +
                                                    projet.reseaux[projet.reseau_actif].links[pivot].nd.ToString() + " " + 
                                                    projet.reseaux[projet.reseau_actif].links[pivot].temps.ToString() +
                                                    " " + projet.reseaux[projet.reseau_actif].links[pivot].cout.ToString() +
                                                    " " + projet.reseaux[projet.reseau_actif].links[pivot].tmap.ToString()+'\n' +
                                                    "pred:" + projet.reseaux[projet.reseau_actif].links[predecesseur].no.ToString() + " " +
                                                    projet.reseaux[projet.reseau_actif].links[predecesseur].nd.ToString() + 
                                                    " " + projet.reseaux[projet.reseau_actif].links[predecesseur].temps.ToString() +
                                                    " " + projet.reseaux[projet.reseau_actif].links[predecesseur].cout.ToString() +
                                                    " " + projet.reseaux[projet.reseau_actif].links[predecesseur].tmap.ToString()+'\n';
                                                fich_log.Write(texto);
                                            }
                                            
                                        }
                                    }
                                    //projet.reseaux[projet.reseau_actif].links[pivot].touche = 3;
                                    //Console.WriteLine((touches.Count+calcules.Count).ToString());
                                }
                            fin_gga2:
                                //Console.WriteLine(p.ToString());

                                int arrivee = -1;
                                double cout_fin = 1e38f;
                                if (projet.reseaux[projet.reseau_actif].numnoeud.TryGetValue(p, out value) == true)
                                {
                                    for (j = 0; j < projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].numnoeud[p]].succ.Count; j++)
                                    {
                                        predecesseur = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].numnoeud[p]].succ[j];
                                        if (projet.reseaux[projet.reseau_actif].links[predecesseur].touche != 0 && projet.reseaux[projet.reseau_actif].links[predecesseur].cout < cout_fin)
                                        {
                                            arrivee = predecesseur;
                                            cout_fin = projet.reseaux[projet.reseau_actif].links[predecesseur].cout;

                                        }




                                    }
                                }
                                else
                                {
                                    fich_log.WriteLine("OD error" + libod + ":" + ":" + chaine + ": non existing origin node!");
                                }

                                if (arrivee != -1)
                                {
                                    if (projet.reseaux[projet.reseau_actif].links[arrivee].ligne > 0)
                                    {
                                        projet.reseaux[projet.reseau_actif].links[arrivee].boai += od;
                                        projet.reseaux[projet.reseau_actif].links[arrivee].services[projet.reseaux[projet.reseau_actif].links[arrivee].service].boai = od;
                                        projet.reseaux[projet.reseau_actif].links[arrivee].services[projet.reseaux[projet.reseau_actif].links[arrivee].service].boat += od;
                                    }
                                }
                                else
                                {
                                    fich_log.WriteLine("OD error" + libod + ":" + chaine + ": unreachable origin node!");
                                }

                                pivot = arrivee;
                                string itineraire = "", texte;
                                if (pivot != -1)
                                {
                                    string[] param2 = { "|" }, lignes_corr = null;
                                    if (projet.reseaux[projet.reseau_actif].links[pivot].texte != null)
                                    {

                                        lignes_corr = projet.reseaux[projet.reseau_actif].links[pivot].texte.Split(param2, StringSplitOptions.RemoveEmptyEntries);
                                    }
                                    if (lignes_corr == null)
                                    {
                                        itineraire = "MAP";
                                    }
                                    else
                                    {
                                        itineraire = lignes_corr[0];
                                    }
                                }
                                while (pivot != -1)
                                {
                                    projet.reseaux[projet.reseau_actif].links[pivot].volau += od;
                                    if (projet.reseaux[projet.reseau_actif].links[pivot].pivot != -1 && projet.param_affectation_horaire.sortie_turns == true)
                                    {
                                        Turn virage = new Turn();
                                        virage.arci = pivot;
                                        virage.arcj = projet.reseaux[projet.reseau_actif].links[pivot].pivot;
                                        float value2;
                                        if (transfers.TryGetValue(virage, out value2) == true)
                                        {

                                            transfers[virage] += od;
                                        }
                                        else
                                        {
                                            transfers[virage] = od;
                                        }

                                        //projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].arci[projet.reseaux[projet.reseau_actif].links[pivot].turn_pivot].volau += od;
                                    }
                                    if (projet.reseaux[projet.reseau_actif].links[pivot].service >= 0)
                                    {
                                        projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].volau += od;
                                    }

                                    if (projet.reseaux[projet.reseau_actif].links[pivot].pivot == -1)
                                    {
                                        if (projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0)
                                        {
                                            projet.reseaux[projet.reseau_actif].links[pivot].alij += od;
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].alij = od;
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].alit += od;

                                        }
                                    }
                                    else if (projet.reseaux[projet.reseau_actif].links[pivot].ligne != projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].ligne)
                                    {
                                        if (projet.reseaux[projet.reseau_actif].links[pivot].ligne > 0)
                                        {
                                            projet.reseaux[projet.reseau_actif].links[pivot].alij += od;
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].alij = od;
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].alit += od;

                                        }
                                        if (projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].ligne > 0)
                                        {
                                            projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].boai += od;
                                            projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].services[projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].service].boai = od;
                                            projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].services[projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].service].boat += od;
                                        }

                                    }
                                    if (projet.param_affectation_horaire.sortie_chemins == true)
                                    {
                                        texte = libod + ";" + p + ";" + q + ";" + jour.ToString("0") + ";" + horaire.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[pivot].no].i;
                                        texte += ";" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[pivot].nd].i;
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].ligne.ToString("0");
                                        if (projet.reseaux[projet.reseau_actif].links[pivot].service >= 0)
                                        {
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].numero.ToString("0");
                                        }
                                        else
                                        {
                                            texte += ";-1";
                                        }
                                        texte += ";" + (-projet.reseaux[projet.reseau_actif].links[pivot].h + horaire).ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].h.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].tveh.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].tmap.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].tatt.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].tcor.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].ncorr.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].tatt1.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].cout.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].l.ToString("0.000");
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].pole;
                                        texte += ";" + od.ToString("0.00");
                                        if (projet.reseaux[projet.reseau_actif].links[pivot].ligne != -1)
                                        {
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].boai.ToString("0.000");
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].alij.ToString("0.000");
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].boai = 0;
                                            projet.reseaux[projet.reseau_actif].links[pivot].services[projet.reseaux[projet.reseau_actif].links[pivot].service].alij = 0;

                                        }
                                        else
                                        {
                                            texte += ";0";
                                            texte += ";0";
                                        }
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].texte;
                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].type;

                                        texte += ";" + projet.reseaux[projet.reseau_actif].links[pivot].ttoll.ToString("0.000");


                                        fich_sortie2.WriteLine(texte);



                                    }
                                    if (projet.reseaux[projet.reseau_actif].links[pivot].pivot != -1)
                                    {
                                        if (projet.reseaux[projet.reseau_actif].links[pivot].ligne != projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].ligne)
                                        {
                                            string[] param2 = { "|" }, lignes_corr = null;
                                            if (projet.reseaux[projet.reseau_actif].links[pivot].texte != null)
                                            {


                                                lignes_corr = projet.reseaux[projet.reseau_actif].links[projet.reseaux[projet.reseau_actif].links[pivot].pivot].texte.Split(param2, StringSplitOptions.RemoveEmptyEntries);
                                            }
                                            if (lignes_corr == null)
                                            {
                                                itineraire = itineraire + "|MAP"; ;
                                            }
                                            else
                                            {
                                                itineraire = itineraire + "|" + lignes_corr[0];
                                            }
                                        }
                                    }
                                    pivot = projet.reseaux[projet.reseau_actif].links[pivot].pivot;
                                }
                                if (arrivee != -1)
                                {
                                    texte = libod + ";" + p + ";" + q;
                                    texte += ";" + jour.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].h.ToString("0.000");
                                    texte += ";" + horaire.ToString("0.000");
                                    texte += ";" + (horaire - projet.reseaux[projet.reseau_actif].links[arrivee].h).ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tveh.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tmap.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tatt.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tcor.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].ncorr.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tatt1.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].cout.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].l.ToString("0.000");
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].pole;
                                    texte += ";" + od.ToString("0.00");
                                    //itineraire = "MAP," + itineraire;
                                    texte += ";" + itineraire;
                                    texte += ";" + projet.param_affectation_horaire.nb_pop;
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].ttoll.ToString("0.000");



                                    fich_od.WriteLine(texte);

                                    if (projet.param_affectation_horaire.sortie_noeuds == true)
                                    {
                                        foreach (node n in projet.reseaux[projet.reseau_actif].nodes)
                                        {
                                            float tmax = 1e38f;
                                            String type_arc = "";
                                            int which_tmax = -1;
                                            link troncon = new link();
                                            for (int s = 0; s < n.succ.Count; s++)
                                            {
                                                troncon = projet.reseaux[projet.reseau_actif].links[n.succ[s]];
                                                if (troncon.cout <= tmax && troncon.touche != 0 && (troncon.ligne <= 0 || projet.param_affectation_horaire.sortie_temps == 2))
                                                {
                                                    tmax = troncon.cout;
                                                    which_tmax = n.succ[s];
                                                    type_arc = troncon.type;
                                                    
                                                }

                                            }
                                            if (which_tmax > 0 && tmax <= projet.param_affectation_horaire.temps_max)
                                            {
                                                if (filtre.Contains(type_arc) || filtre.Count == 0)
                                                {
                                                    texte = libod + ";" + p + ";" + q;
                                                    texte += ";" + jour.ToString("0.000");
                                                    texte += ";" + n.i;
                                                    texte += ";" + horaire.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].h.ToString("0.000");
                                                    texte += ";" + (horaire - projet.reseaux[projet.reseau_actif].links[which_tmax].h).ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].tveh.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].tmap.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].tatt.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].tcor.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].ncorr.ToString("0");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].tatt1.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].cout.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].l.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].pole;
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[which_tmax].ttoll.ToString("0.000");

                                                    fich_noeuds.WriteLine(texte);
                                                }
                                            }
                                        }
                                    }
                                    if (projet.param_affectation_horaire.sortie_temps == 0)
                                    {
                                        network reseau = projet.reseaux[projet.reseau_actif];
                                        double som_detour = 0; double nb_detour = 0; double som_oiseau = 0;
                                        double d_oiseau, d_link;
                                       
                                        foreach (link li in reseau.links)
                                        {
                                            d_oiseau = Math.Pow(Math.Pow((reseau.nodes[reseau.numnoeud[q]].x - reseau.nodes[li.no].x), 2) + Math.Pow((reseau.nodes[reseau.numnoeud[q]].y - reseau.nodes[li.no].y), 2), 0.5);
                                            d_link = Math.Pow(Math.Pow((reseau.nodes[li.no].x - reseau.nodes[li.nd].x), 2) + Math.Pow((reseau.nodes[li.no].y - reseau.nodes[li.nd].y), 2), 0.5);

                                            if (d_oiseau > 500 & d_oiseau - d_link <= 500)
                                            {

                                                if (reseau.nodes[reseau.numnoeud[q]].x > 0 && reseau.nodes[reseau.numnoeud[q]].y > 0 && reseau.nodes[li.no].x > 0 && reseau.nodes[li.no].y > 0)
                                                {
                                                    if (li.h > 0)
                                                    {
                                                        som_detour += li.h;
                                                        som_oiseau += Math.Pow(Math.Pow((reseau.nodes[reseau.numnoeud[q]].x - reseau.nodes[li.no].x), 2) + Math.Pow((reseau.nodes[reseau.numnoeud[q]].y - reseau.nodes[li.no].y), 2), 0.5);
                                                        nb_detour++;
                                                    }
                                                }
                                            }
                                        }
                                        fich_detour.WriteLine(q + ";" + som_detour.ToString() + ";" + som_oiseau.ToString() + ";" + nb_detour.ToString());

                                    }


                                    if (projet.param_affectation_horaire.sortie_temps > 0)
                                    {
                                        for (i = 0; i < projet.reseaux[projet.reseau_actif].links.Count; i++)
                                        {

                                            arrivee = i;
                                            if (filtre.Contains(projet.reseaux[projet.reseau_actif].links[arrivee].type) || filtre.Count == 0)
                                            {

                                                if (projet.reseaux[projet.reseau_actif].links[arrivee].touche != 0 && (projet.reseaux[projet.reseau_actif].links[arrivee].ligne < 0 || projet.param_affectation_horaire.sortie_temps == 2))
                                                {
                                                    texte = libod + ";" + q;
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[arrivee].no].i;
                                                    texte += "-" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[arrivee].nd].i;
                                                    texte += ";" + (projet.reseaux[projet.reseau_actif].links[arrivee].ligne).ToString("0");
                                                    texte += ";" + i.ToString("0");
                                                    texte += ";" + jour.ToString("0");


                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].h.ToString("0.000");
                                                    texte += ";" + horaire.ToString("0.000");
                                                    link arc = new link();
                                                    arc = projet.reseaux[projet.reseau_actif].links[arrivee];
                                                    float ti;
                                                    if (arc.ligne < 0)
                                                    {
                                                        ti = horaire - (arc.h + arc.temps * projet.param_affectation_horaire.coef_tmap[arc.type]);
                                                    }
                                                    else
                                                    {
                                                        ti = horaire - (arc.h + (arc.services[arc.service].hf - arc.services[arc.service].hd));
                                                    }
                                                    texte += ";" + ti.ToString("0.000");
                                                    
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tveh.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tmap.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tatt.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tcor.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].ncorr.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].tatt1.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].cout.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].l.ToString("0.000");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].pole;
                                                    texte += ";" + od.ToString("0.00");
                                                    //texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].texte;
                                                    /*texte += ";" + projet.param_affectation_horaire.texte_cveh;
                                                    texte += ";" + projet.param_affectation_horaire.texte_cwait;
                                                    texte += ";" + projet.param_affectation_horaire.texte_cmap;
                                                    texte += ";" + projet.param_affectation_horaire.texte_cboa;
                                                    texte += ";" + projet.param_affectation_horaire.texte_coef_tmap;
                                                    texte += ";" + projet.param_affectation_horaire.texte_tboa;
                                                    texte += ";" + projet.param_affectation_horaire.nb_jours;*/
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].pivot.ToString("0");
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].type;
                                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[arrivee].ttoll.ToString("0.000");
                                                    texte += ";" + (horaire - projet.reseaux[projet.reseau_actif].links[arrivee].h).ToString("0.000");
                                                    //                                itineraire = "MAP," + itineraire;
                                                    if (projet.reseaux[projet.reseau_actif].links[arrivee].cout <= projet.param_affectation_horaire.temps_max)
                                                    {
                                                        if (test_temps_per_min_arrivee(projet, arrivee) == true)
                                                        {
                                                            fich_sortie.WriteLine(texte);
                                                        }


                                                    }
                                                }
                                                else if (projet.reseaux[projet.reseau_actif].links[arrivee].touche == 0 && projet.param_affectation_horaire.sortie_isoles == true)
                                                {
                                                    texte = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[arrivee].no].i;
                                                    texte += "-" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[arrivee].nd].i;
                                                    texte += ";" + (projet.reseaux[projet.reseau_actif].links[arrivee].ligne).ToString("0");
                                                    texte += ";" + i.ToString("0");
                                                    fich_isoles.WriteLine(texte);

                                                }
                                            }
                                        }
                                    }
                                }
                            }

                        }
                        DateTime t2 = DateTime.Now;
                        fich_log.WriteLine("Computation end time: " + t2.ToString("dddd dd MMMM yyyy HH:mm:ss.fff"));

                        fich_log.WriteLine("Computation duration:" + t2.Subtract(t1).TotalSeconds + " sec");
                        fich_log.Close();

                        fich_sortie.Close();
                        fich_sortie2.Close();
                        fich_od.Close();
                        fich_noeuds.Close();
                        fich_detour.Close();
                        fich_isoles.Close();




                        for (i = 0; i < projet.reseaux[projet.reseau_actif].links.Count; i++)
                        {
                            if (projet.reseaux[projet.reseau_actif].links[i].volau > 0 || projet.reseaux[projet.reseau_actif].links[i].boai > 0 || projet.reseaux[projet.reseau_actif].links[i].alij > 0)
                            {
                                string texte = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[i].no].i;
                                texte += ";" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[i].nd].i + ";" + projet.reseaux[projet.reseau_actif].links[i].ligne.ToString("0");
                                texte += ";" + projet.reseaux[projet.reseau_actif].links[i].volau.ToString("0.00");
                                texte += ";" + projet.reseaux[projet.reseau_actif].links[i].boai.ToString("0.00");
                                texte += ";" + projet.reseaux[projet.reseau_actif].links[i].alij.ToString("0.00");
                                texte += ";" + projet.reseaux[projet.reseau_actif].links[i].texte;
                                texte += ";" + projet.reseaux[projet.reseau_actif].links[i].type;
                                texte += ";" + projet.reseaux[projet.reseau_actif].links[i].toll.ToString("0.000");

                                fich_result.WriteLine(texte);
                            }

                        }


                        fich_result.Close();
                        //projet.reseaux.Remove(projet.reseaux[projet.reseau_actif]);
                        if (projet.param_affectation_horaire.sortie_services == true)
                        {
                            System.IO.StreamWriter fich_services = new System.IO.StreamWriter(projet.param_affectation_horaire.nom_sortie + "_services.txt", false, System.Text.Encoding.UTF8);
                            string texte = "";
                            fich_services.WriteLine("i;j;ligne;service;hd;hf;regime;volau;boia;alij;texte;type");
                            for (i = 0; i < projet.reseaux[projet.reseau_actif].links.Count; i++)
                            {
                                if (projet.reseaux[projet.reseau_actif].links[i].services.Count > 0)
                                {
                                    for (j = 0; j < projet.reseaux[projet.reseau_actif].links[i].services.Count; j++)
                                    {
                                        if (projet.reseaux[projet.reseau_actif].links[i].services[j].volau > 0)
                                        {
                                            texte = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[i].no].i;
                                            texte += ";" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[i].nd].i + ";" + projet.reseaux[projet.reseau_actif].links[i].ligne.ToString("0");
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[i].services[j].numero;
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[i].services[j].hd;
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[i].services[j].hf;
                                            texte += ";" + projet.reseaux[projet.reseau_actif].nom_calendrier[projet.reseaux[projet.reseau_actif].links[i].services[j].regime];
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[i].services[j].volau.ToString("0.00");
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[i].services[j].boat.ToString("0.00");
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[i].services[j].alit.ToString("0.00");
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[i].texte;
                                            texte += ";" + projet.reseaux[projet.reseau_actif].links[i].type;
                                            fich_services.WriteLine(texte);

                                        }
                                    }
                                }


                            }
                            fich_services.Close();

                        }
                        if (projet.param_affectation_horaire.sortie_turns == true)
                        {
                            System.IO.StreamWriter fich_turns = new System.IO.StreamWriter(projet.param_affectation_horaire.nom_sortie + "_transferts.txt", false, System.Text.Encoding.UTF8);
                            string texte = "";
                            //int k=0;
                            fich_turns.WriteLine("j;i;lignei;k;lignek;textei;textek;volau");

                            foreach (Turn virage in transfers.Keys)
                            {

                                if (transfers[virage] > 0)
                                {
                                    texte = projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[virage.arci].nd].i;

                                    texte += ";" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[virage.arci].no].i;
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[virage.arci].ligne;
                                    texte += ";" + projet.reseaux[projet.reseau_actif].nodes[projet.reseaux[projet.reseau_actif].links[virage.arcj].nd].i;
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[virage.arcj].ligne;
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[virage.arci].texte;
                                    texte += ";" + projet.reseaux[projet.reseau_actif].links[virage.arcj].texte;
                                    texte += ";" + transfers[virage];
                                    fich_turns.WriteLine(texte);
                                }










                            }
                            fich_turns.Close();

                        }

                        flux.Close();
                        fichier_matrice.Close();
                    }


                    //algorithme de Dijkstra

                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra
                    //algorithme de Dijkstra


                    //algorithme de Dijkstra

                    else if (projet.param_affectation_horaire.algorithme == 2)
                    {


                    }
                }
                
            
            }
        }

        public class vecteur
        {
            public List<float> d = new List<float>(0);

        }


        public class Turn
        {
            public int arci, arcj;

            public override bool Equals(Object virage)
            {
                if (arci == ((Turn)virage).arci && arcj == ((Turn)virage).arcj)
                {
                    return true;
                }
                else
                {
                    return false;
                }
            }
            public override int GetHashCode()
            {
                return arci.GetHashCode() ^ arcj.GetHashCode();
            }

        }

        public class turn
        {
            public int numero;
            public float temps;
            public bool is_valid = false;
            //public float volau=0;

        }

        public class node
        {
            public float x, y, tempst = 1e38f, tmap = 0, tatt, temps, cout, ncor, ttoll;
            public string i;
            public bool ci = false, is_valid = true, is_visible = false, is_intersection = false;
            public List<int> pred = new List<int>();
            public List<int> succ = new List<int>();
            //public List<float> ui = new List<float>();
            public string texte;
            public string pole;
        }
        public class Link_num
        {
            public String i, j;
            public int line;
            public override bool Equals(object num_link)
            {
                if (i == ((Link_num)num_link).i && j == ((Link_num)num_link).j && line == ((Link_num)num_link).line)
                {
                    return true;
                }
                else
                {
                    return false;
                }
            }
            public override int GetHashCode()
            {
                return (i.GetHashCode() ^ j.GetHashCode() ^ line.GetHashCode());
            }
        }
        public class link
        {
            public float longueur, temps, cout, v0, vsat, tatt, tcor, tveh, tmap, tatt1, a, b, n, volau, lanes, h, l, alij, boai, ncorr, toll = 0, ttoll;
            public int no, nd, service, vdf, touche, pivot, ligne, turn_pivot = -1;//,nb_voies;
            public bool is_queue, is_valid = true;
            //public List<turn> arci = new List<turn>();
            //public List<turn> arcj = new List<turn>();
            //public List<float> ul = new List<float>();
            public List<Service> services = new List<Service>();
            public string texte, modes, pole, type = "0";
            /*public float fd(float volau, float len, float precha, float cap, float v0, float a, float b, float n)
            {
                float vc, t0, delay;
                t0 = len / v0;
                vc = (volau + precha) / cap;
                if (vc < 1)
                {
                    delay = t0 * (a - b * vc) / (a - vc);
                }
                else
                {
                    delay = t0 * ((a * (1f - b)) / (n * (a - 1f) * (a - 1f))) * (float)Math.Pow(vc, n) + (n * (a - b) * (a - 1f) - a * (1f - b)) / (n * (a - 1f) * (a - 1f));
                }
                return delay;
            }*/
        }


        public class matrix
        {
            public string nom;
            public List<vecteur> o = new List<vecteur>(0);

        }

        public class network
        {
            public string nom;
            public List<link> links = new List<link>(20000);
            public List<node> nodes = new List<node>(10000);
            public float xl = 1e38f, xu = -1e38f, yl = 1e38f, yu = -1e38f;
            public List<matrix> matrices = new List<matrix>();
            public Dictionary<string, int> numnoeud = new Dictionary<string, int>();
            public Dictionary<string, int> num_calendrier = new Dictionary<string, int>();
            public List<string> nom_calendrier = new List<string>();
            public Dictionary<string, string> noms_arcs = new Dictionary<string, string>();
            public int max_type = 0, nbturns = 0, nbservices = 0;
        }

        public class etude
        {
            public string nom;
            public int reseau_actif;
            public List<network> reseaux = new List<network>();
            public Param_affectation_horaire param_affectation_horaire = new Param_affectation_horaire();

        }

        public class Param_affectation_horaire
        {
            public string nom_reseau, nom_matrice, nom_sortie, nom_penalites;
            public Dictionary<String, float> coef_tmap = new Dictionary<String, float>();
            public Dictionary<String, float> cmap = new Dictionary<String, float>();
            public Dictionary<String, float> cwait = new Dictionary<String, float>();
            public Dictionary<String, float> cboa = new Dictionary<String, float>();
            public Dictionary<String, float> tboa = new Dictionary<String, float>();
            public Dictionary<String, float> tboa_max = new Dictionary<String, float>(1);
            public Dictionary<String, float> cveh = new Dictionary<String, float>(1);
            public Dictionary<String, float> ctoll = new Dictionary<String, float>(1);
            public float param_dijkstra, pu;
            public bool sortie_chemins, demitours = true, sortie_services = false, sortie_turns = false, test_OK = false, sortie_noeuds = true, sortie_isoles = false;
            public int sortie_temps;
            public int algorithme = 1;
            public float max_nb_buckets = 10000;
            public int nb_jours = 0;
            public string texte_coef_tmap;
            public string texte_cmap;
            public string texte_cwait;
            public string texte_cboa;
            public string texte_tboa;
            public string texte_tboa_max;
            public string texte_cveh, texte_toll;
            public float tmapmax, temps_max = 120;
            public int nb_pop = 0;
            public string texte_filtre_sortie = "";
        }

        public class Service
        {
            public int numero;
            public float hd, hf, delta = 0, boai = 0, alij = 0, alit = 0, boat = 0, volau = 0;
            public int regime;
        }

        public class suivant
        {
            public List<int> classe = new List<int>();

        }



        public class Node
        {
            public string i = "";
            public float x = 0, y = 0, tempst = 1e38f, tmap = 0, tatt, temps, cout, ncor, ttoll;
            public string name = "";
            public string pole;
            public List<int> in_nodes = new List<int>();
            public List<int> out_nodes = new List<int>();
            public void addincoming(int i)
            {
                this.in_nodes.Add(i);
            }
            public void addoutgoing(int i)
            {
                this.out_nodes.Add(i);
            }

        }

        public class Link
        {

        }

        public static bool test_temps_per_min_depart(etude projet, int arrivee)
        {

            bool reponse = true;
            link arc = new link();
            arc = projet.reseaux[projet.reseau_actif].links[arrivee];
            int  ni;
            ni = arc.no;
            foreach (int k in projet.reseaux[projet.reseau_actif].nodes[ni].succ)
            {
                int nj = projet.reseaux[projet.reseau_actif].links[k].nd;
                int ligne = projet.reseaux[projet.reseau_actif].links[k].ligne;
                if ((nj == arc.nd ) && !(arc.ligne == ligne) && projet.reseaux[projet.reseau_actif].links[k].touche != 0)
                {
                    if (arc.cout > projet.reseaux[projet.reseau_actif].links[k].cout)
                        {
                        reponse = false;
                        }
                 }
            }
            return reponse;
        }
        public static bool test_temps_per_min_arrivee(etude projet, int arrivee)
        {

            bool reponse = true;
            link arc = new link();
            arc = projet.reseaux[projet.reseau_actif].links[arrivee];
            int nj;
            nj = arc.nd;
            foreach (int k in projet.reseaux[projet.reseau_actif].nodes[nj].pred)
            {
                int ni = projet.reseaux[projet.reseau_actif].links[k].no;
                int ligne = projet.reseaux[projet.reseau_actif].links[k].ligne;
                if ((ni == arc.no) && !(arc.ligne == ligne) && projet.reseaux[projet.reseau_actif].links[k].touche!=0)
                {
                    if (arc.cout > projet.reseaux[projet.reseau_actif].links[k].cout)
                    {
                        reponse = false;
                    }
                }
            }
            return reponse;
        }
    }
}