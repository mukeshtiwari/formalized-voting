open Lib
open Printf
       
let show_bool = function 
  | Lib.True -> "True"
  | Lib.False -> "False"

let rec nat_int = function
  | O -> 0
  | S n' -> 1 + nat_int n'

let rec ocamllist = function
  | Nil -> []
  | Cons (h, t) -> h :: ocamllist t
                                  
let show_nat n = string_of_int (nat_int n)         

let rec ocaml_pos = function
  | Lib.XH -> 1
  | p ->
     let rec ocaml_help t c =
       match t with
       | Lib.XH -> c
       | Lib.XO r -> ocaml_help r (2 * c)
       | Lib.XI r -> c + ocaml_help r (2 * c)
     in ocaml_help p 1

let ocaml_z = function
  | Lib.Z0 -> 0
  | Lib.Zpos p -> ocaml_pos p
  | Lib.Zneg p -> -1 * ocaml_pos p

let show_z p = string_of_int (ocaml_z p)
                             
let show_cand = function
  | Lib.A -> "A"
  | Lib.B -> "B"
  | Lib.C -> "C"
  | Lib.D -> "D"

let compare x y =
  match x, y with
  | Lib.A, Lib.A | Lib.B, Lib.B | Lib.C, Lib.C | Lib.D, Lib.D -> true
  | _, _ -> false

let compare_pair x y =
  match x, y with
  | Lib.Pair (x1, y1), Lib.Pair (x2, y2) -> compare x1 x2 && compare y1 y2
                                                                     
let rec cross_prod_orig = function
  | [] -> []
  | h :: t as v -> List.map (fun x -> (h, x)) v @ cross_prod_orig t
                                                                  
let show_cand_pair (c1, c2) = "(" ^ show_cand c1 ^ "," ^ show_cand c2 ^ ")"

let compare_truth x y =
  match x, y with
  | Lib.True, Lib.True | Lib.False, Lib.False -> true
  | _, _ -> false
  
let show_coclosed f l =
  "[" ^ String.concat
          ","
          (List.map show_cand_pair  
          (List.filter (fun (x, y) -> compare_truth (f (Lib.Pair (x, y))) Lib.True)
                       (cross_prod_orig l))) ^ "]"
                          
let show_help f c = show_cand c ^ show_nat (f c)
  
let show_ballot f =
  String.concat " " (List.map (fun c -> show_help f c) (ocamllist Lib.cand_all))
                
let bool_b = function
  | Nil -> true
  | _ -> false

let show_list_inv_ballot = function
  | Nil ->"[]"
  | Cons (b, Nil) -> "[" ^ show_ballot b ^ "]"
  | Cons (b, _) -> "[" ^ show_ballot b ^ ",..]"

let rec cross_prod = function
  | [] -> []
  | h :: t -> List.map (fun x -> (h, x)) t @ cross_prod t
                                                     
let show_pair c1 c2 n = show_cand c1 ^ show_cand c2 ^ ":" ^ show_z n                                           
let show_marg m =
  "[" ^ String.concat
          " "
          (List.map (fun (x, y) -> show_pair x y (m x y)) (cross_prod (ocamllist Lib.cand_all)))
  ^ "]"
      
let rec show_path = function
  | Lib.UnitT (x, y) -> show_cand x ^ " --> " ^ show_cand y
  | Lib.ConsT (x, _, _, p) -> show_cand x ^ " --> " ^ show_path p

let rec show_winner g x xs =
  match xs with
  | [] -> ""
  | y :: ys -> if compare x y then show_winner g x ys
               else
                 match (g y) with
                 | ExistT (u, Pair (v, ExistT (f, _))) ->
                    "   for " ^ show_cand y ^ ": " ^ "path " ^
                      show_path v ^ " of strenght "  ^ show_z u ^  ", " ^
                        string_of_int (1 + ocaml_z u) ^ 
                          "-" ^ "coclosed set: " ^ show_coclosed f (ocamllist Lib.cand_all)
                       ^ (if ys = [] then " " else "\n")  ^ show_winner g x ys 
                         
let show_loser g x =
  match g with
  | ExistT (u, ExistT (c, Pair (p, ExistT (f, _)))) ->
     "   exists " ^ show_cand c ^ ": " ^ "path " ^ show_path p ^ " of strength "
     ^ show_z u ^ ", " ^ show_z u ^ "-" ^ "coclosed set: " ^ show_coclosed f (ocamllist Lib.cand_all)
      
let show_cand f x =
  match f x with
  | Inl g -> "winning: " ^ show_cand x ^ "\n" ^ show_winner g x (ocamllist Lib.cand_all)
  | Inr h -> "losing: " ^ show_cand x ^ "\n" ^ show_loser h x
                                                          
let rec add_string = function
  | 0 -> ""
  | n -> "-" ^ add_string (n - 1)
                            
let underline s = s ^ "\n" ^ add_string (String.length s) ^ "\n"

let rec show_count = function
  | Lib.Ax (_, _) -> ""
  | Lib.Cvalid (u, us, m, nm, inbs, c) ->
     show_count c ^ underline (
       "V: [" ^ show_ballot u ^ (if bool_b us then "]" else ",..]")  ^
         ", I:  " ^ show_list_inv_ballot inbs  ^ ", M: " ^ show_marg m ) 
  | Lib.Cinvalid (u, us, m, inbs, c)  ->
     show_count c ^ underline (
       "V: [" ^ show_ballot u ^
         (if bool_b us then "]" else ",..]") ^ ", I: " ^ show_list_inv_ballot inbs ^ 
           ", M: " ^ show_marg m )
  | Lib.Fin (m, ls, p, f, c) ->
     show_count c ^ underline (
       "V: [], I: " ^ show_list_inv_ballot ls ^ ", M: " ^ show_marg m )
     ^ String.concat "\n" (List.map (fun x -> show_cand f x) (ocamllist Lib.cand_all))
     ^ "\n"

