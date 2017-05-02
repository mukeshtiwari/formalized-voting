open Lib
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

           
let cc c =
  match c with
  | 'A' -> A
  | 'B' -> B
  | 'C' -> C
  | 'D' -> D
  | _ -> failwith "failed"
            
let balfun l = 
   match l with
   | [(A, b1); (B, b2); (C, b3); (D, b4)] -> 
      let
        f c = match c with
        | A -> b1
        | B -> b2
        | C -> b3
        | D -> b4
        | _ -> failwith "failed to match"
      in  f
   | _ -> failwith "failed to match pattern" 



let _ = 
  let e = Parser.prog Lexer.lexeme (Lexing.from_channel stdin) in
  let w = List.map (fun x -> List.map (fun (a, b) -> (cc a, ocamlnat b)) x) e in
  let v = List.map (fun x -> balfun x) w in
  match schulze_winners_pf (ocamlcoq v) with
  | ExistT (f, ExistT (y, _)) ->  Format.printf "%s\n"  (show_bool (f A))
                                        
  

     
