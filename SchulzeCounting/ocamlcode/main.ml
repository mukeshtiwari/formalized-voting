open Lib
open Printf
open Str
        
       
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
        let f A = b1 in 
        let f B = b2 in
        let f C = b3 in
        let f D = b4 in  f
   | _ -> failwith "failed to match pattern" 


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
  

  
