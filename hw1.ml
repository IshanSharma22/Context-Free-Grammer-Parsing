open List;;

type ('nonterminal, 'terminal) symbol =
  | N of 'nonterminal
  | T of 'terminal;;

let rec subset a b = match a with
    [] -> true
    | head::rlist -> if (List.mem head b) then (subset rlist b) else false;;

let equal_sets a b = if (subset a b && subset b a) then true else false;;

let rec set_union a b = List.append a b;;

let rec set_intersection a b = match b with
	| [] -> []
	| head::rlist -> if (List.mem head a) then head::(set_intersection rlist a)
		  else (set_intersection rlist a);;


let rec set_diff a b = match a with
| [] -> []
| head::rlist -> if (List.mem head b) then (set_diff rlist b)
		  else head::(set_diff rlist b);;

let rec computed_fixed_point eq f x = 
	if  eq x (f x) then x
	else computed_fixed_point eq f (f x);;

let leftItem (x, _) = x;;
let rightItem (_, x) = x;;

let termSymb symbol = match symbol with
| N symbol -> true
| T symbol -> false

let rec rule_helper rules list_h = match rules with
| [] -> []
| head::rlist -> if  not ( List.exists ( (=) (N(leftItem head))) list_h) 
                 then rule_helper rlist list_h
                 else head::(rule_helper rlist list_h);;

let fliter_help g reach = (N(leftItem g))::find_all termSymb (List.concat(List.map rightItem (rule_helper (rightItem g) reach)));;

let filter_reachable g = (leftItem g, rule_helper (rightItem g)(computed_fixed_point (equal_sets) (fliter_help g)([(N(leftItem g))])));;

