open List;;

type ('nonterminal, 'terminal) symbol =
  | N of 'nonterminal
  | T of 'terminal

type ('nonterminal, 'terminal) parse_tree =
  | Node of 'nonterminal * ('nonterminal, 'terminal) parse_tree list
  | Leaf of 'terminal


let rec convertHelper syb rules =
	match rules with 
	| [] -> []
	| head::tail -> if (fst head) != syb then
			convertHelper syb tail
		else
			snd head::(convertHelper syb tail);;

let convert_grammar gram1 = 
	match gram1 with
	| (xpres, rules) -> (xpres, function syb -> convertHelper syb rules)
	;;


let rec parHelper treeIn = match treeIn with
	| [] -> []
	| head::rest -> List.append (parse_tree_leaves head) (parHelper rest)

and parse_tree_leaves tree = 
	match tree with
	| Leaf le -> [le]
	| Node (_, restNodes) -> (parHelper restNodes);;


let retHd (x::_) = x
let retTl (_::x) = x

let rec opHelper parSym rules parAccep parfrag parOpts parFunc =
	match parOpts with
	| [] -> None
	| head::rest ->
		let tmp = parFunc ( List.append head parSym) rules parAccep parfrag in
		match tmp with 
		| None -> opHelper parSym rules parAccep parfrag rest parFunc
		| a -> if ([a] != []) then a else None

let rec matHelper
	(parSym : ('nonterm,'term) symbol list) 
	(rules : ('nonterm -> ('nonterm, 'term) symbol list list)) 
	(parAccep : ('term list -> 'a option))
	(parfrag : 'term list)
	: 'a option =

	if (parSym != []) then  
	
		match (retHd parSym) with 
		| N nonterm -> 
			let parOpts = rules nonterm in
			if not (parOpts = []) then
			opHelper (retTl parSym) rules parAccep parfrag parOpts matHelper
			else
			opHelper (retTl parSym) rules parAccep parfrag [[]] matHelper


		| T term ->
			match parfrag with 
			|[] -> None
			| head::rest -> 
			if not (term = head) then 
				None
			else
				matHelper (retTl parSym) rules parAccep (retTl parfrag)
				

	else parAccep parfrag
	
;;

let make_matcher gram = 
	matHelper [N (fst gram)] (snd gram)
;;

let rec opHelperP 
	(parSym : ('nonterm,'term) symbol list) 
	(rules : ('nonterm -> ('nonterm, 'term) symbol list list)) 
	(parfrag : 'term list)
	(nonterm : 'nonterm) 
	(parOpts : ('nonterm,'term) symbol list list) 
	func =
	match parOpts with
	| [] -> None 
	| headOp::restOp -> if ([headOp] != [] || [restOp] != []) then let tmp = func (List. append headOp parSym) rules parfrag in
		match tmp with 
		| None -> opHelperP parSym rules parfrag nonterm restOp func 
		| Some x -> Some ((nonterm, headOp) :: x) 
	else None

let rec derHelper
	(parSym : ('nonterm,'term) symbol list) 
	(rules : ('nonterm -> ('nonterm, 'term) symbol list list)) 
	(parfrag : 'term list)
	: ('nonterm * ('nonterm,'term) symbol list) list option =

	if not (parfrag != [] || parSym != []) then Some [] 

	else if not (parSym != []) then None 
	
	else
	match (retHd parSym) with 
	| N nonterm -> 
		let parOpts = rules nonterm in
		if not (parOpts = []) then
			opHelperP (retTl parSym) rules parfrag nonterm parOpts derHelper
		else 
			opHelperP (retTl parSym) rules parfrag nonterm [[]] derHelper
	
	| T term ->
		match parfrag with
		| [] -> None
		| head::rest -> 
			if not (term = head) then
				None
			else
				derHelper (retTl parSym) rules (retTl parfrag)
;;

exception Invalid_Output_That_Should_Not_Occur;;

let rec treeAux 
	(defderiv : ('nonterm * ('nonterm,'term) symbol list) list) 
	: ('nonterm * ('nonterm,'term) symbol list) list * ('nonterm,'term) parse_tree =

	let rec ptree_iterator 
		(defderiv : ('nonterm * ('nonterm,'term) symbol list) list)
		(righth : ('nonterm,'term) symbol list) 
		: ('nonterm * ('nonterm,'term) symbol list) list * ('nonterm,'term) parse_tree list =
			match righth with 
			| [] -> defderiv, []
			| head::rest -> if ([head] != [] || [rest] != [] ) then
				match head with
				| T term -> 
					let tmp = ptree_iterator defderiv rest in
					(match tmp with (dervRem, subtrees) -> dervRem, ((Leaf	term) :: subtrees))		

				| N nonterm -> 
					let tmpex = treeAux defderiv in
					match tmpex with (dervRem, nodeCur) -> let tmp = ptree_iterator dervRem rest in
					match tmp with (dervRemP, treeS) -> dervRemP, (nodeCur :: treeS)	
				else defderiv, []
	in

	match defderiv with 
	| [] -> raise (Invalid_Output_That_Should_Not_Occur)
	| head::rest -> if ([head] != [] || [rest] != [] ) then match head with | (lefth, righth) ->
		let tmp = ptree_iterator rest righth in
		match tmp with | (dervRem, subtrees) ->
			dervRem, Node (lefth, subtrees)
		else raise (Invalid_Output_That_Should_Not_Occur)
;;


let auxParse gram frag =
	let defderiv = derHelper [N (fst gram)] (snd gram) frag in
	match defderiv with
	| None -> None
	| Some b-> 
		let tmp = treeAux b in
		match tmp with (x, ptree) -> if([tmp] != []) then Some ptree else None
	
;;

let make_parser gram = 
	auxParse gram
;;

