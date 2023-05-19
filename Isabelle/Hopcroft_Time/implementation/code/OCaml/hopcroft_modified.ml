let check_reachability automaton is_final initial= 
  let cardinal_sigma=Array.length automaton in 
  let cardinal_q=Array.length (automaton.(0)) in 
  let tableau_etat=(Array.create cardinal_q 0) in 
  let tableau_etat_inv=(Array.create cardinal_q 0) in
    for i=1 to (cardinal_q-1) do 
      (tableau_etat).(i)<-i; (tableau_etat_inv).(i)<-i
    done; 
    let echange indice1 indice2=
      let elt1=(tableau_etat).(indice1) in 
      let elt2=(tableau_etat).(indice2) in
	(tableau_etat_inv).(elt1)<-indice2;
	(tableau_etat_inv).(elt2)<-indice1; 
	(tableau_etat).(indice1)<-elt2;
	(tableau_etat).(indice2)<-elt1 in
    let reachable=ref 0 in 
    let reachable_and_done=ref (-1) in
      echange 0 initial; 
      while (!reachable_and_done)<(!reachable) do
	incr reachable_and_done; 
	for i=0 to (cardinal_sigma -1) do
	  let succ_i= automaton.(i).(tableau_etat.(!reachable_and_done)) in 
	    (if (tableau_etat_inv).(succ_i)>(!reachable)
	     then
	       (incr reachable; 
		echange ((tableau_etat_inv).(succ_i)) (!reachable))) done done;
(if (!reachable)=(cardinal_q-1) then () else
(output_string stderr ("L'automate n'est pas accessible.("^(string_of_int(!reachable+1)) ^" etats sont accessibles)\n"); flush stderr));
let new_automate=Array.make_matrix cardinal_sigma (!reachable+1) 0 in let new_final=Array.make (!reachable+1) false in
for q=0 to (!reachable) do ((if is_final.((tableau_etat).(q))
then new_final.(q)<-true); for a=0 to (cardinal_sigma-1) do
new_automate.(a).(q)<- tableau_etat_inv.(automaton.(a).((tableau_etat).(q)))
done) done;
(new_automate, new_final,0);;




(* Algorithme de Hopcroft: 
automaton: int [] [] (lettre, etat) 
final_array: bool [] (etat) 
initial: int (etat initial) *)

exception EarlyQuit

let hopcroft_aux (automaton,final_array,initial)=(
 (* initialisation des structures*) 
  let compteur_t=ref 0 in
  let compteur_swap=ref 0 in
  let compteur_change_classe=ref 0 in
  let cardinal_sigma=Array.length automaton in
    (* nombre de lettre*)
  let cardinal_q=Array.length (automaton.(0)) in 
    (*nombre d'etats*)
  let checked=Array.make_matrix (cardinal_sigma) (cardinal_q) 0 in 
  let date_inv=Sys.time() in 
  let transition_inverse= (Array.make_matrix cardinal_sigma cardinal_q []) in
    for i=0 to (cardinal_q-1) do for j=0 to (cardinal_sigma-1) do let succ=(automaton).(j).(i) in
      (transition_inverse).(j).(succ)<-(i::(transition_inverse.(j).(succ)))
    done done;
(* Construction de la fonction de transition inverse: 
transition_inverse: (int list) [] [] (lettre, etat) *)

flush stderr;
let tableau_etat=(Array.create cardinal_q 0) in let tableau_etat_inv=(Array.create cardinal_q 0) in
for i=1 to (cardinal_q -1) do 
(tableau_etat).(i)<-i; 
(tableau_etat_inv).(i)<-i
done;

(*construction des tableaux tableau_etat et tableau_etat_inv 
tableau_etat: int [] avec tableau_etat.(i)=i et 
tableau_etat_inv: int [] avec tableau_etat_inv.(i)=i *)

let table_etat_classe=Array.create (cardinal_q) 0 in 
(*construction du tableau qui fournit la classe d'un etat:
table_etat_classe: int [] *)

let taille_max=ref 511 in 
(*nombre max de classe a priori: on augmente dynamiquement la taille des
objets si la valeur limite est atteinte*)

let table_classe_liste=ref (Array.create (!taille_max) (0,0)) in 
(* table_classe_liste: int*int [] (classe) contient les deux indices asso
ciés à une classe*)

let table_pointeur_classe_liste=ref (Array.create (!taille_max) 0) in 
(*table_pointeur_classe_liste: int [] ou (int [])*??? *)

let liste_L=ref [] in 
(* liste_: int list (liste chainée qui contient la liste des classes à traiter)*)

let echange indice1 indice2= (let elt1=(tableau_etat).(indice1) in
let elt2=(tableau_etat).(indice2) in 
  (tableau_etat_inv).(elt1)<-indice2; 
  (tableau_etat_inv).(elt2)<-indice1; 
  (tableau_etat).(indice1)<-elt2; 
  (tableau_etat).(indice2)<-elt1) in

(*Fonction permettant d'echanger les elements d'indices indice1 et indice2 dans le tableau tableau_etat et mise a jour du tableau tableau_etat_inv *)

let build_initial_partition ()= 
let bot=ref 0 in 
let up=ref (cardinal_q -1) in
while (!bot)<=(!up) do 
  if (final_array).(tableau_etat.(!bot)) then
    (echange (!bot) (!up); decr up)
  else (incr bot) done;
!table_classe_liste.(1)<-(0,!up); 
!table_classe_liste.(0)<-(!bot,cardinal_q-1);
!table_pointeur_classe_liste.(1)<-(!up);
!table_pointeur_classe_liste.(0)<-(cardinal_q -1); 
for k=0 to (!up) do
table_etat_classe.(tableau_etat.(k))<-1 done;
for k=(!bot) to (cardinal_q-1) do table_etat_classe.(tableau_etat.(k))<-0
done; 

(if (!up-0=(-1)) then
(output_string stderr ("L'automate minimal a: 1 etat\nLa minimisation a duree: 0 s\nLa sortie a duree: 0 s\n");
flush stderr; 
output_string stderr (string_of_int (cardinal_sigma)^"\n1\n0\n"); 
for i=0 to (cardinal_sigma-1) do
output_string stderr ("0\t0\t"^(string_of_int i)^"\n") done;
output_string stderr ("0\n"); 
flush stdout; raise EarlyQuit ));

(if (cardinal_q-1-(!bot)=(-1)) then
(output_string stderr ("L'automate minimal a: 1 etat\nLa minimisation a duree: 0 s\nLa sortie a duree: 0 s\n");
flush stderr; 
output_string stderr (string_of_int (cardinal_sigma)^"\n1\n0\n");
for i=0 to (cardinal_sigma-1) do output_string stderr ("0\t0\t"^(string_of_int i)^"\n")
done;
 flush stderr; 
raise EarlyQuit));

(if (cardinal_q-1-(!bot))<(!up) then
liste_L:=[0]
else
liste_L:=[1];) 
in build_initial_partition ();

let pointeur_partition=ref 1 in 
(*pointeur vers le numero de la derniere classe creee*)
let resize ()= let ancienne_taille=(!taille_max+1) in
table_classe_liste:=(Array.append (!table_classe_liste) (Array.create (ancienne_taille) (0,0)));
table_pointeur_classe_liste:=(Array.append (!table_pointeur_classe_liste)
(Array.create (ancienne_taille) 0)); 
taille_max:=((ancienne_taille)*2-1) in
(*fonction permettant de redimensionner les objets lorsque pointeur_partition pointe vers taille_max*)
(*Fonctions de minimisation*)
let casse_par_rapport q_1 a= let (j1,j2)=((!table_classe_liste).(q_1)) in let classe_antecedents=ref [] in let antecedents_dans_q_1=ref [] in
((for l=j1 to (j2) do let (ap)=checked.(a).(tableau_etat.(l)) in
checked.(a).(tableau_etat.(l))<-(succ (ap)); List.iter
(function x->incr compteur_t; let classe_x=(table_etat_classe).(x) in let (i1,i2)=(!table_classe_liste).(classe_x) in
if i1=i2 then () else
(if classe_x=q_1 then
(antecedents_dans_q_1:=x::(!antecedents_dans_q_1))
else (let indice_x=(tableau_etat_inv).(x) in
let pointeur= (!table_pointeur_classe_liste).(classe_x) in (((if pointeur=i2 then
(classe_antecedents:= (classe_x::(!classe_antecedents))));
((incr compteur_swap; echange indice_x pointeur));
(!table_pointeur_classe_liste).(classe_x)<- (pointeur-1))))))
((transition_inverse).(a).(((tableau_etat).(l))))
done); let ante=(!antecedents_dans_q_1) in
(if ante=[] then () else
(classe_antecedents:=(q_1::(!classe_antecedents)); List.iter
(function x-> let indice_x=(tableau_etat_inv).(x) in let pointeur=(!table_pointeur_classe_liste).(q_1) in
(incr compteur_swap; echange indice_x pointeur);
(!table_pointeur_classe_liste).(q_1)<- (pointeur-1)) ante)));
let fonction_casse=function h-> (let (i1,i2)=(!table_classe_liste).(h) in
let pointeur=(!table_pointeur_classe_liste).(h) in if pointeur=(i1-1) then ((!table_pointeur_classe_liste).(h)<-i2) else (incr pointeur_partition;
let new_class=(!pointeur_partition) in (if (new_class)=(!taille_max) then resize()); (if (i2-pointeur-1)<=(pointeur-i1)
then
((!table_classe_liste).(h)<-(i1,pointeur); (!table_classe_liste).(new_class)<-(pointeur+1,i2); for j=(pointeur+1) to i2 do
incr compteur_change_classe; (table_etat_classe).((tableau_etat).(j))<-
(new_class) done;
(!table_pointeur_classe_liste).(h)<-(pointeur);
(!table_pointeur_classe_liste).(new_class)<-i2)
else
((!table_classe_liste).(h)<-(pointeur+1,i2); (!table_classe_liste).(new_class)<-(i1,pointeur); for j=(i1) to pointeur do
incr compteur_change_classe; (table_etat_classe).((tableau_etat).(j))<-
(new_class) done;
(!table_pointeur_classe_liste).(h)<-(i2); (!table_pointeur_classe_liste).(new_class)<-
pointeur); liste_L:=(new_class)::(!liste_L) ))) in
List.iter fonction_casse (!classe_antecedents);

in 
let hopcroft ()=
  let rec aux=function 
    |(q::t)->liste_L:=t; for letter=0 to (cardinal_sigma-1) do
	casse_par_rapport (q) (letter) done;
	aux (!liste_L) 
    |[]->() in
    aux (!liste_L) in 
  hopcroft ();
  
let representant q=(let (i,_)=(!table_classe_liste).(q) in 
		      tableau_etat.(i)) in
let sort_resultat= ()
in sort_resultat);;

let hopcroft x =
  try (hopcroft_aux x) with EarlyQuit -> ()

let rec mk_assoc n l = match l with 
    [] -> []
  | e :: l -> (e, n) :: (mk_assoc (n+1) l)

let build_automaton (q, a, d, i, f) = 
  let cardinal_sigma=List.length a in
  let cardinal_Q=(List.fold_left max 0 q) + 1 in
  let initial_init=List.hd i in
  let automaton_array_init=Array.make_matrix cardinal_sigma (cardinal_Q) 0 in
  let final_init=Array.make (cardinal_Q) false in
  let _ = List.iter (fun q -> (final_init.(q) <- true)) f in
  let aa = mk_assoc 0 a in
  let _ = List.iter (fun (q1, a, q2) ->
             automaton_array_init.(List.assoc a aa).(q1) <- q2) d in
   check_reachability automaton_array_init final_init initial_init;;





