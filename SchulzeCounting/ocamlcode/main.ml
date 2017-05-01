open Lib
open Printf
open Str
open Parser
open Lexer
       
let rec ocamlcoq l = 
  match l with
  | [] -> Nil
  | h :: t -> Cons (h, (ocamlcoq t))   

let rec ocamlnat n =
  match n with
  | 0 -> O
  | _ -> S (ocamlnat (n -1))
           
let balfun l = 
   match l with
   | [(A, b1); (B, b2); (C, b3); (D, b4)] -> 
      let
        f c = match c with
        | A -> b1
        | B -> b2
        | C -> b3
        | D -> b4
      in  f
   | _ -> failwith "failed to match pattern" 

(*
let input_line_opt ic =
  try Some (input_line ic)
  with End_of_file -> None
                        
let read_lines ic =
  let rec aux acc =
    match input_line_opt ic with
    | Some line -> aux (line::acc)
    | None -> (List.rev acc)
  in
  aux []
  
let lines_of_file filename =
  let ic = open_in filename in
  let lines = read_lines ic in
  close_in ic;
  lines 

 

let process_input filename =
  let lines = lines_of_file filename in
  List.map (fun x -> Str.split (Str.regexp ";") x) lines

let lst =
  [[(A,3);(B,1);(C,2);(D,4)];
   [(A,1);(B,0);(C,4);(D,3)];
   [(A,3);(B,1);(C,2);(D,4)];
   [(A,2);(B,3);(C,3);(D,4)];
   [(A,3);(B,1);(C,2);(D,4)];
   [(A,1);(B,2);(C,3);(D,4)];
   [(A,1);(B,2);(C,3);(D,4)];
   [(A,1);(B,2);(C,2);(D,4)];
   [(A,1);(B,2);(C,2);(D,4)];
   [(A,1);(B,3);(C,2);(D,4)]]

let l =
  let w = List.map (fun x -> List.map (fun (a, b) -> (a, ocamlnat b)) x) lst in
  let v = List.map (fun x -> balfun x) w in
  ocamlcoq v
 *)

                   
let rec print_list = function 
    [] -> ()
  | e::l -> match e with
            | True -> printf "%B" true ; print_string " "; print_list l
            | False -> printf "%B" false ; print_string " " ; print_list l
(*
       
let _ =
  
  let l = open_in stdin in
  let e = Parser.prog Lexer.lexeme (Lexing.from_string l) in
  printf "%s" e
         
  match schulze_winners_pf e with
  | ExistT (f, ExistT (y, _)) -> print_list (List.map f [A; B; C; D]) 
          *)                                  
  

  
   
