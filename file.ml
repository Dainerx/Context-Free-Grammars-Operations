
(*Authors: 	BEN GHORBEL Oussama
		   	CHEKINI Hakima
		   	
			Étudiants en deuxième année, Spécialité informatique
			École d’ingénieurs Sup Galilée – Paris 13
			2018 - 2019
			*)

type terminal = A'|B'|C'|D'|E'|F'|G'|H'|I'|J'|K'|L'|M'|N'|O'|P'|Q'|R'|S'|T'|U'|V'|W'|X'|Y'|Z'|EmptyTerminal;;
type nonTerminal = A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|EmptyNonTerminal;;
type entity = terminal * nonTerminal;;
type regleProd = Imp of nonTerminal * string;;

(* global variables *)
let grammar = [Imp(A,"BF"); Imp(B,"ccD"); Imp(B,"d"); Imp(D,"E"); Imp(F,"ga")];;
let grammar1 = [Imp(A,"bC"); Imp(A,"ccd"); Imp(B,"abDf"); Imp(C,"a"); Imp(F,"abL"); Imp(L,"bcA")];;
let grammar2 = [ Imp(S, "aSBS"); Imp(S, "SbadS"); Imp(S,"$"); Imp(S,"abf"); Imp(A, "AbrA"); Imp(A,"$")];;
let listTerminals = [A';B';C';D';E';F';G';H';I';J';K';L';M';N';O';P';Q';R';S';T';U';V';W';X';Y';Z'];;
let listNonTerminals = [A;B;C;D;E;F;G;H;I;J;K;L;M;N;O;P;Q;R;S;T;U;V;W;X;Y;Z];;
let listNonTerminalsChar = ['A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';'N';'O';'P';'Q';'R';'S';'T';'U';'V';'W';'X';'Y';'Z'];;
let listTerminalsChar = ['a';'b';'c';'d';'e';'f';'g';'h';'i';'j';'k';'l';'m';'n';'o';'p';'q';'r';'s';'t';'u';'v';'w';'x';'y';'z'];;

(*
Description:
	Cette fonction retourne l'index d'un element dans une lisite si il exisite sinon -1.
Entrée:
	- Une liste
	- Un élément
	- Un entier
Sortie:
	- Un entier
Exemple:
	# indexOfElement ['a';'g'] 'g' 0;;
	- : int = 1
*)

let rec indexOfElement l x n = 
	if List.mem x l = false then -1
	 else
		let curr = List.nth l n in 
		if  curr = x then n
		else 
			let m = n+1 in 
		    indexOfElement l x m;;

(* 
Description: 
	Cette fonction permet d'afficher un message suivi par une liste de chaines de caractères entrés en paramètres.
Entrée
	- Une chaine de caractères
	- Une liste de chaines de caractères
*)
let print_strings name l =
print_string name;
print_string "[";
List.iter (fun i -> print_string i; print_string "; ") l;
print_string "]"

let print_chars name l =
print_string name;
print_string "[";
List.iter (fun i -> print_char i; print_string "; ") l;
print_string "]"



(*
Description:
	Cette fonction permet de convertir un caractère en nonTerminal ou un terminal tout dépend du caractère
Entrée: 
	- Un caractère
Sortie:
	- Un couple de type entity (terminal * nonTerminal)
Exemple:
	#convert 'a';;
	- : terminal * nonTerminal = (A', EmptyNonTerminal)
	# convert 'A';;
	- : terminal * nonTerminal = (EmptyTerminal, A)
*)

let convert c =  
if (List.mem c listNonTerminalsChar) then (EmptyTerminal,(List.nth listNonTerminals (indexOfElement listNonTerminalsChar c 0)))
else if (List.mem c listTerminalsChar) then ((List.nth listTerminals (indexOfElement listTerminalsChar c 0)),EmptyNonTerminal)
else (EmptyTerminal, EmptyNonTerminal);;


(*
Description:
	Cette fonction permet de convertir un nonTerminal en un caractère. 
Entrée: 
	- Un nonTerminal
Sortie:
	- Un caractère
Exemple:
	# reverse_convert_nonTerminal B;;
	- : char = 'B'
*)

let reverse_convert_nonTerminal c =  
(List.nth listNonTerminalsChar (indexOfElement listNonTerminals c 0));;


(*
Description:
	Cette fonction permet de convertir un terminal en un caractère. 
Entrée: 
	- Un terminal
Sortie:
	- Un caractère
Exemple:
	# reverse_convert_terminal A';;
	- : char = 'a'
*)
let reverse_convert_terminal c =  
(List.nth listTerminalsChar (indexOfElement listTerminals c 0));;


(*
Description: 
	Cette fonction boucle sur la totalité de grammaire en commençant par la tête et lors de chaque itération teste 
	si le nonTerminal en question est accessible de la coté gauche.
Entrée: 
	- Un nonTerminal
	- Une grammaire 
	- Un entier
Sorite:
	- Un bool
Exemple:
	# accessibleAcc B grammar 0;;
	- : bool = true
*)
let rec accessibleAcc x grammaire n = match grammaire with
[] -> false
| Imp(ter, reg)::tailGram -> 
	if ( n = 0  && (x = ter ) ) then true
	else
		let y = reverse_convert_nonTerminal x in
		if (String.contains reg y) then true 
		else
			let m = n + 1 in  
			accessibleAcc x tailGram m;;

(*
Description: 
	Cette fonction en se utilisant accessibleAcc retourne vrai dans le cas où il exisite un chemin qui mène à un nonTerminal entré en paramètre,
	faux sinon.
Entrée: 
	- Un nonTerminal
	- Une grammaire 
Sortie:
	- Un bool
Exemple:
	# accessible B grammar;;
	- : bool = true
	# accessible F grammar;;
	- : bool = false
*)
let rec accessible x grammaire = accessibleAcc x grammaire 0;;


(* 
Description: 
	Cette fonction sert à tester si un nonTerminal, entré en paramètre, peut être deduit par des terminaux. 
	Vrai si c'est le cas, faux sinon.
Entrée:
	- Un nonTerminal
	- Une grammaire
Sortie:
	- Un bool
Exemple: 
	# can_go_further E grammar;;
	- : bool = false
	# can_go_further A grammar;;
	- : bool = true
*)
let rec can_go_further nonT grammaire = match grammaire with
	[] -> false
	|Imp(ter, reg)::tailGram -> 
		if ter = nonT then true 
		else
			 can_go_further nonT tailGram;;

(*
Description: 
	Cette fonction prend un nonTerminal et fait toutes les déductions possible en se basant sur 
	la grammaire en retournant une liste. 
Entrée:
	- Un nonTerminal
	- Une grammaire
Sortie: 
	- Une liste de chaine de caractères
Exemple:
	# deduce B grammar;;
	- : string list = ["ccD"; "d"]
*)

let rec deduce x grammaire = match grammaire with
[] -> []
|Imp(ter, reg)::tailGram -> 
		if x = ter then reg::(deduce x tailGram)
		else deduce x tailGram;;

(*
Description:
	Cette fonction prend une chaine de caractères, un index et une liste de chaine de caractères en paramètre, 
	afain de retourner une liste comme résultat après avoir remplacer le caractère à la position index par toutes
	les chaines de caractères présentes dans la liste en paramètre.
Entrée:
	- Une chaine de caractère
	- Un entier
	- Une liste des chaines de caractères
Sortie:
	- Une liste de chaine de caractères
Exemple:
	# divide "ocaml" 2 ["jj"; "pp"];;
	- : string list = ["ocjjml"; "ocppml"]
*)

let rec divide str index res =
	let leng =  String.length str in 
	if index > leng then []
	else 
		match res with 
		[]-> []
		|x::ll -> 
		let left = String.sub str 0 index in
		 let ind = index +1 in
		 let lengR = leng - ind in
		 let right = String.sub str ind  lengR 
		 in  (String.concat x [left; right])::divide str index ll;;


(* 
Description: 
	Cette fonction, en utilisant divide et deduce, permet de substituter un nonTerminal donné en paramètre avec tous 
	ses deductions dans une chaine de caractères. Elle retourne une liste qui contient tous les chaines de caractères
	possibles à former.
Entrée:
	- Un caractère
	- Une chaine de caractères
	- Une grammaire
Sortie:
	- Une liste de chaine de caractères
Exemple:
	# substitute 'B' "jhjBl" grammar;;
	- : string list = ["jhjccDl"; "jhjdl"]
*)

let substitute c str grammaire =
	let (ter, nT) = convert c in 
		if nT = EmptyNonTerminal then 
		[]
		else 
		    let index = String.index str c in
			let ded =  deduce nT grammaire in  
			divide str index ded;;
(*
Description: 
	Cette fonction permet de supprimer les doublons dans une liste des éléments
Entrée:
	- Une liste
Sortie:
	- Une liste
Source: 
	- https://gist.github.com/23Skidoo/1664038
Exemple:
	# remove_dups [1;2;1;3;3];;
	- : int list = [1; 2; 3]
*)

let rec remove_dups lst= match lst with
| [] -> []
| h::t -> h::(remove_dups (List.filter (fun x -> x<>h) t))


(*
Description:
	Cette fonction prend en paramètre une chaine de caractères et renvoie une liste de tous les caractères
	de cette chaine
Entrée:
	- Une chaine de caractères
Sortie:
	- Une liste de caractères
Exemple:
	# explode "aze";;
	- : char list = ['a'; 'z'; 'e']
*)
let explode str =
  let rec explode_inner cur_index chars = 
    if cur_index < String.length str then
      let new_char = str.[cur_index] in
      explode_inner (cur_index + 1) (chars @ [new_char])
    else chars in
  explode_inner 0 []



(*
Description:
	Cette fonction retourne une liste qui contient tous les nonTerminaux trouvés dans la liste 
	de caractères entrée en paramètre.
Entrée:
	- Une liste de caractères
Sortie:
	- Une liste de caractères
Exemple:
	# getAllNonTerminals ['A';'d';'h';'h';'B';'l';'P'];;
	- : char list = ['A'; 'B'; 'P']
*)

let rec getAllNonTerminals l = match l with 
	| [] -> []
	| c::ll -> 	
			let (ter, nt) = convert c in
			if (List.mem c listNonTerminalsChar) then 
					c::(getAllNonTerminals ll)
				else 
					getAllNonTerminals ll;;

(*
Description:
	Cette fonction retourne une liste qui contient tous les nonTerminaux deductifs trouvés dans la liste 
	de caractères entrée en paramètre.
Entrée:
	- Une liste de caractères
Sortie:
	- Une liste de caractères
Exemple:
	# getNonTerminals ['A';'d';'h';'h';'B';'l';'P'];;
	- : char list = ['A'; 'B']
*)
let rec getNonTerminals l = match l with 
	| [] -> []
	| c::ll -> 	
			let (ter, nt) = convert c in
			if (List.mem c listNonTerminalsChar && can_go_further nt grammar) then 
					c::(getNonTerminals ll)
				else 
					getNonTerminals ll;;

(* 
Description: 
	Cette fonction prend en paramètre trois listes et retourne les deux derniers:
	1. l: une liste qui contient des chaines de caractères où on cherche à savoir les quelles contiennent que 
	des terminaux et les quelles contiennent des nonTerminaux qu'on peut substituer  
	2. yet: une liste qu'on va construire qui va contenir toutes les chaines de caractères 
	qui contiennent des nonTerminaux qu'on peut substituer
	3. finished: une liste qu'on va construire qui va contenir toutes les chaines de caractères qui contiennent 
	que des terminaux
Entrée:
	- Une liste de chaine de caractères
	- Une liste de chaine de caractères (R)
	- Une liste de chaine de caractères (R)
Sortie:
	- Un couple de listes de chaine de caractères
Exemple: 
	# yet_finished ["azeD";"aeee";"B"] [] [];;
	- : string list * string list = (["B"; "azeD"], ["aeee"])
*)
let rec yet_finished l yet finished = match l with
| [] -> (yet,finished)
| head::tail -> let string_as_list = explode head in
				let list_non_terminals = getNonTerminals string_as_list in
				if ( list_non_terminals = [] ) then yet_finished tail yet (List.append [head] finished)  
				else yet_finished tail (List.append [head] yet) finished


(* 
Description: 
	Cette fonction substitue les nonTerminaux contenus dans une chaine de caractères entrée en paramètre
	par toutes les deductions possible en assurant que les chaines de caractères résultantes ont aucun
	nonTerminal deductif. Le résultat de cette fonction est son 3ème paramètre qui est une liste de chaines
	de caractères qui va contenir tous les resultats possibles.
Entrée:
	- Une chaine de caractères
	- Une liste de chaines de caractères
	- Une liste de chaines de caractères
	- Un entier
Sortie:
	- Une liste de chaines de caractères
Exemple:
	all_results_for "Bc" [] [];;
	- : string list = ["dc"; "ccec"]
*)
let rec all_results_for str yet finished i = match (yet,finished) with
| (_,_) ->  if str="" then finished 	
		else
			let ii = i + 1 in
			let string_as_list = explode str in
			let list_non_terminals = getNonTerminals string_as_list in
			let len = List.length yet in
			let upper_bound = len - 1 in 
			if ((List.length list_non_terminals) = 0) then (* this str contains only terminals *) 
				let f = List.append [str] finished in (* We need to add this str to the final result *)
				if (ii>upper_bound) then
					all_results_for "" yet f ii
				else
					all_results_for (List.nth yet ii) yet f ii (* We need another string to work on so we'll go to the next index*)
			else 
				let c = List.nth list_non_terminals 0 in (*get me the first nonTerminal we need to substitute *)
				let l = substitute c str grammar in
				let (y,f) = yet_finished l [] [] in
				if ((List.length y) = 0) then 
					if (ii>upper_bound) then
						all_results_for "" (List.append yet y) (List.append finished f) ii
					else
						all_results_for (List.nth yet ii) (List.append yet y) (List.append finished f) ii
				else
					all_results_for (List.nth y 0) (List.append yet y) (List.append finished f) i;;

let rec pre_final go_on = match go_on with
|[] -> []
|head::tail -> let finished = all_results_for head [] [] 0 in
				List.append finished (pre_final tail);;

(* 
Description:
	Cette fonction en utilisant pre_final et all_results_for retourne tous les résultats finals possibles 
	pour un nonTerminal entré en paramètre
Entrée:
	- Un nonTerminal
Sortie:
	- Une liste de chaine de caractères
Exemple:
	# get_final_results_for_nonT A;;
	- : string list = ["dga"; "ccEga"]
*)
let get_final_results_for_nonT nonT =
	let result = remove_dups (pre_final (deduce nonT grammar)) in
	result;;

(* 
Description:
	Cette fonction permet d'itérer une liste de chaine de caractères entrée en paramètre et retourne vrai si 
	toutes les chaines sont formés par seulement des terminaux. Faux sinon.
Entrée:
	- Une chaine de caractère
Sortie:
	- Un bool
Exemple:
	# is_productiveAcc ["aze";"bb"];;
	- : bool = true
	# is_productiveAcc ["Aez";"bb";"Ea"];;
	- : bool = false
*)
let rec is_productiveAcc result = match result with 
[] -> true
|head::tail ->  let string_as_list = explode head in
				let listOfNonTerminals = (getAllNonTerminals string_as_list) in 
				let len = (List.length listOfNonTerminals) in
				if len = 0 then
					(is_productiveAcc tail)
				else
					false;;

(* 
Description:
	Cette fonction en utilisant is_productiveAcc retourne vrai si un nonTerminal est productif, sinon faux. 
Entrée:
	- Un nonTerminal
Sortie:
	- Un bool
Exemple:
	# is_productive A;;
	- : bool = false
	# is_productive F;;
	- : bool = true
*)
let is_productive nonT = 
	is_productiveAcc (get_final_results_for_nonT nonT);;


(*
Description:
	Cette fonction permet de retourner le nombre d'occurence d'un caractère dans une liste de caractère, les deux 
	entrés en paramètre.
Entrée:
	- Un caractère 
	- Une liste de caractères
	- Un entier
Sortie:
	- Un entier
Exemple:
	# occ 'e' ['a';'e';'e';'b';'e'] 0;;
	- : int = 3
*)
let rec occ c l n = match l with 
[] -> n
|head::tail -> if head=c then 
					let m = n+1 in 
					occ c tail m
				else 
					occ c tail n;;

(* 
Description:
	Cette fonction prend en paramètre un caractère non terminal ‘c’, une chaîne de caractère ‘str’ 
	ainsi qu’un entier ‘n’ et renvoie une liste de chaînes de caractère où le caractère ‘c’ 
	rentré en paramètre est remplacé par une chaîne vide, le remplacement se fera une fois par 	chaîné.
Entrée:
	- Un caractère 
	- Une chaine de caractères 
	- Un entier 
Sortie:
	- Une liste de chaines de caractères
Exemple:
	replaceWithEps 'S' "aSaSb" 0;;
	- : string list = ["aSaSb"; "aaSb"; "aSab"]
	replaceWithEps 'S' "SabS" 0;;
	- : string list = ["SabS"; "abS"; "Sab"]
*)
let replaceWithEps c str n  = 
	let string_as_list = explode str in
	let nb = occ c string_as_list 0 in
	let ll = [str] in 
	  let rec replaceWithEps_inner c str n nb ll=
		if nb <> 0  then 
	   		let index = String.index_from str n c in
			let l = (divide str index [""]) in
			let s = List.hd l in
			let m = index + 1 in
			let nbb = nb - 1 in 
	     	replaceWithEps_inner c str m nbb (ll@[s])
	 else ll in replaceWithEps_inner c str 0 nb ll


(*
Description:
	Cette fonction prend en paramètre un caractère non terminal ‘c’, une chaîne de caractère ‘str’ ainsi 4
	qu’un entier ‘n’ et renvoie une liste de chaînes de caractère où le caractère ‘c’ rentré en 
	paramètre est remplacé par une chaîne vide, le remplacement se fera une fois par chaîné.
	Elle commence par récupérer le nombre d’occurrences  ‘nb’ de ‘c’ dans la chaîne ‘str’ , si le 
	caractère ‘c’ apparaît toujours dans la chaîne ‘str’, elle récupère son index et le remplace par 
	une chaîne vide  " ", et réitère l’opération en commençant par le caractère qui suit l’index du dernier ‘c’ trouvé.
Entrée:
	- Un caractère
	- Une chaine de caractères
Sortie:
	- Une chaine de caractères
Exemple:
	# replaceAllEps 'S' "aSbSa";;
	- : string = "aba"
*)
let replaceAllEps c str =
	let rec replaceAllEps_inner c str =
	let string_as_list = explode str in
	let nb = occ c string_as_list 0 in
	if nb <> 0 then 
			let index = String.index str c in
			let l = (divide str index [""]) in
			let s = List.hd l in
			replaceAllEps_inner c s 
	else str in replaceAllEps_inner c str

(*
Description:
	Cette fonction prend en paramètre un caractère non terminal ‘c’ ainsi qu‘une chaîne de caractères 
	et renvoie une liste de chaînes de caractères où les caractères ‘c’ se trouvant dans la chaîne ‘str’ 
	sont substitués par une chaîne vide. Cette fonction a pour but d’éliminer la règle de production S→Epsilon 
	en substituant le caractère non terminal dans chaque chaîne par une chaîne vide.
	Elle commence par récupérer les la liste de chaîne de caractères où chaque caractère ‘c’ qui figure dans 
	la chaîne ‘str’ est substitué uniquement une fois pour chaque chaîne retournée en faisant appel à la fonction 
	replaceWithEps, ensuite, elle récupère la chaîne de caractères où tous les caractères ‘c’ se trouvant dans 
	la chaîne ‘str’ sont substitués par une chaîne vide. Le résultat final sera la concaténation des deux listes.
Entrée:
	- Un caractère
	- Une chaine de caractères	
Sortie:
	- Une liste de chaines de caractères
Exemple:
	 combineWithoutEps 'S' "aSbSa";;
	- : string list = ["aSbSa"; "abSa"; "aSba"; "aba"]
*)
let combineWithoutEps c str =
	let a = replaceWithEps c str 0 in
	let b = replaceAllEps c str in
	match a with
	[] -> [b]
	|x::tail-> a@[b];;

(*
Description:
	Cette fonction prend en paramètre une grammaire et renvoie la liste des productions où le caractère non terminal 
	donne epsilon.
	Elle commence par vérifier si la liste est vide, elle renvoie une liste vide, sinon elle concatène la règle 
	de production qui contient ’$’ ‘Epsilon’ dans le reste de la liste en faisant un appel récursif.
Entrée:
	- Une grammaire
Sortie:
	- Une grammaire
Exemple:
	existeEps grammar1;; 
	- : regleProd list = [Imp (S, "$"); Imp (A, "$")]
*)
let rec existeEps grammaire = match grammaire with
[]-> []
|Imp(ter, reg)::tailGram -> if String.contains reg '$'
							 then (Imp(ter, reg))::existeEps tailGram 
							else existeEps tailGram ;;
(*
Description:
	Cette fonction prend en paramètre une grammaire ainsi qu’un caractère non terminal ‘c’ et renvoie 
	une liste de chaîne de caractères qui contiennent le caractère donné en paramètre en vérifiant si 
	le caractère non terminal de la règle de production est le même que celui passé en 	paramètre.
Entrée:
	- Une grammaire
	- Un caractère
Sortie:
	- Une liste de chaines de caractères
Exemple:
	 stringTochange  grammar1 'A';;
	- : string list = ["aAbS"; "bAaa"]
*)
let rec stringTochange grammaire c = match grammaire with
[]-> []
|Imp(ter, reg)::tailGram -> 
		let (t, cc) = convert c in 
		if ((String.contains reg c) && (ter = cc))
							 then reg::(stringTochange tailGram c) 
							else stringTochange tailGram c;;
(*
Description:
	Cette fonction prend en paramètre une liste de chaîne de caractères ainsi qu’un caractère non terminal ‘c’ 
	et renvoie une liste de chaîne de caractères.
	Elle fait appel à la fonction combineWithoutEps pour chaque élément de la liste qui élimine les règles 
	de productions c→Epsilon, et fait un appel récursif sur le reste de la liste.
Entrée:
	- Une liste de chaines de caractères 
	- Un caractère
Sortie:
	- Une liste de chaines de caractères 
Exemple:
	 substituteNonTerEps ["ASBS"; "SUS"] 'S';;
	- : string list = ["ASBS"; "ABS"; "ASB"; "AB"; "SUS"; "US"; "SU"; "U"]
*)
let rec substituteNonTerEps listString c =
	match listString with
	|[] -> []
	| s::tail -> (combineWithoutEps c s )@substituteNonTerEps tail c;;

(*
Description:
	Cette fonction prend en paramètre une liste de chaînes de caractères ainsi qu’un caractère 	non terminal ‘c’ 
	et renvoie une grammaire ( une liste avec des règles de productions).
	Pour chaque chaîne de caractère, elle crée une règle de production en utilisant le 	constructeur Imp avec 
	le caractère c donné en paramètre et cette chaîne.
Entrée:
	- Une liste de chaines de caractères
	- Un caractère
Sortie:
	- Une grammaire
Exemple:
	#  createRegle ["ASBS"; "ABS"; "ASB"; "AB"] 'S';;
	- : regleProd list = [Imp (S, "ASBS"); Imp (S, "ABS"); Imp (S, "ASB"); Imp (S, "AB")]
*)
let rec createRegle listString c = 
	let (t, n) = convert c in
	match listString with
	[]->[]
	|x::ll->(Imp(n, x))::createRegle ll c;;



(*
Description:
	Cette fonction prend en paramètre une grammaire ainsi qu’un non terminal et renvoie une liste de règles de 
	productions.
	Elle commence par récupérer les chaînes de caractères qui contiennent le caractère donné en paramètre 
	(les règles de productions dont le non terminal est ‘c’ et la chaîne de caractères 	contient ‘c’). 
	Ensuite, pour chaque chaîne elle fait appel à substituteNonTerEps et pour finir, elle fait appel à createRegle 
	pour avoir en sortie la forme d’une grammaire (liste de règles de productions).
Entrée:
	- Une grammaire
	- Un caractère
Sortie:
	- Une grammaire
Exemple:
	# getRegleWithoutEps grammar1 S;;
	- : regleProd list =
	[Imp (S, "aSBS"); Imp (S, "aBS"); Imp (S, "aSB"); Imp (S, "aB");
	 Imp (S, "SbadS"); Imp (S, "badS"); Imp (S, "Sbad"); Imp (S, "bad")]

*)
let getRegleWithoutEps grammaire c =
	let xx = reverse_convert_nonTerminal c in
	let strchg = stringTochange grammaire xx in 
	let subNTer = substituteNonTerEps strchg xx in
	let creatR = createRegle subNTer xx in
	match creatR with
	[]-> []
	|g::tail -> creatR;;


(*
Description:
	Cette fonction prend en paramètre une grammaire ainsi qu’un caractère ‘c’ et renvoie une liste de règles 
	de productions dont la chaîne de caractère ne contient pas epsilon et ne contient pas le caractère donné 
	en paramètre.
Entrée:
	- Une grammaire
	- Un caractère
Sortie:
	- Une grammaire
# regleWithoutNt grammar1 S;;
- : regleProd list = [Imp (S, "abf")]
*)
let rec regleWithoutNt grammaire c = match grammaire with
[]->[]
|Imp(ter, reg)::tailGram -> 
		let cc = reverse_convert_nonTerminal c in
		     if (String.contains reg cc || String.contains reg '$')
		      then regleWithoutNt tailGram c
			  else (Imp(ter, reg))::(regleWithoutNt tailGram c);;

(*
Description
	Cette fonction prend en paramètre une grammaire et renvoie une liste de règles de productions.
	Elle récupère tous les non terminaux qui donnent un epsilon, et pour chaque non terminal elle récupère 
	et substitue les chaîne de caractères contenant le caractère donné en paramètre en faisant appel à la fonction 
	getRegleWithoutEps.
Entrée:
	- Une grammaire
Sortie:
	- Une grammaire
Exemple:
	#  substituteAllWithoutEps grammar1 [Imp (S, "$"); Imp (A, "$")];;
	- : regleProd list =
	[Imp (S, "aSBS"); Imp (S, "aBS"); Imp (S, "aSB"); Imp (S, "aB");
	Imp (S, "SbadS"); Imp (S, "badS"); Imp (S, "Sbad"); Imp (S, "bad");
 	Imp (A, "AbrA"); Imp (A, "brA"); Imp (A, "Abr"); Imp (A, "br")]
# 

*)
let rec substituteAllWithoutEps grammaire listNt = 
	match listNt with
	[] -> []
	|Imp(x, m)::tailListNt -> (getRegleWithoutEps grammaire x)@substituteAllWithoutEps grammaire tailListNt;;

(*
Description:
	Cette fonction prend en paramètre une grammaire et renvoie une liste de règles en éliminant les epsilons 
	tout en gardant les autres règles.
Entrée:
	- Une grammaire
Sortie:
	- Une grammaire
Exemple:
	# eliminateEps grammar1;;
	- : regleProd list =
	[Imp (S, "aSBS"); Imp (S, "aBS"); Imp (S, "aSB"); Imp (S, "aB");
	 Imp (S, "SbadS"); Imp (S, "badS"); Imp (S, "Sbad"); Imp (S, "bad");
	 Imp (A, "AbrA"); Imp (A, "brA"); Imp (A, "Abr"); Imp (A, "br");
 	Imp (S, "abf"); Imp (A, "AbrA")]
# 

*)

let eliminateEps grammaire = 
	let listNt = existeEps grammaire in
	if List.length listNt <> 0 then
		let Imp(a,b) = List.hd listNt in
		let l0= existeEps grammaire in
		let l1 = substituteAllWithoutEps grammaire l0 in
		let l2 = regleWithoutNt grammaire a in
		if (l2 = [] && l1 = []) then []
	    else l1@l2
	else [];;