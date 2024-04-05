open List
open Char
open Format

exception Not_implemented
exception Parse_exn

(* Data Definitions *)

type token
= LParen
| RParen
| TokTrue
| TokFalse
| TokZero
| TokIf
| TokSucc
| TokPred
| TokIsZero
| TokAnd
| TokOr
| TokNot
| TokPlus

type term
= True
| False
| Zero
| If of term * term * term
| Succ of term
| Pred of term
| IsZero of term
| And of term * term
| Or of term * term
| Not of term
| Plus of term * term

(* Utilities *) 

(* Strings in ocaml are not represented as lists of characters. For lexing and parsing purposes, it's easier to work
with lists of characters. You shouldn't need to touch these functions that convert between the two, but feel free to use them for debugging. *)
let string_to_char_list (s: string) : char list =
  s |> String.to_seq |> List.of_seq
  
let char_list_to_string (cl: char list) : string =
  cl |> List.to_seq |> String.of_seq
  
(* Value Judgements *)

(* Returns true if the term is a numeric value, false otherwise. *)
let rec is_num_val (t: term) : bool = 
  match t with 
  | Zero -> true 
  | Succ t1 -> is_num_val t1
  | _ -> false

(* Returns true if the term is a value, false otherwise. *)
let is_val (t: term) : bool = 
  match t with 
  | True -> true 
  | False -> true 
  | t1 when is_num_val t1 -> true 
  | _ -> false 

(* Lexical Scanner *)

(* nextToken should return the next token from a list of characters, along with the characters thereafter
   - return None if the list of chars is empty
   - skip whitespace characters
   - throw an exception if the characters cannot be tokenized 
  Some basic cases have been given for you. *)
let rec nextToken (cs: char list) : (token * char list) option = 
  match cs with
  | [] -> None
  | ' '::tl -> nextToken tl
  | '('::tl -> Some (LParen, tl)
  | ')'::tl -> Some (RParen, tl)
  | 't'::'r'::'u'::'e'::tl -> Some (TokTrue, tl)
  | 'f'::'a'::'l'::'s'::'e'::tl -> Some (TokFalse, tl)
  | '0'::tl -> Some(TokZero, tl)
  | 'i'::'f'::tl -> Some(TokIf, tl)
  | 'o'::'r'::tl -> Some(TokOr, tl)
  | 'a'::'n'::'d'::tl -> Some(TokAnd, tl)
  | 's'::'u'::'c'::'c'::tl -> Some(TokSucc, tl)
  | 'p'::'r'::'e'::'d'::tl -> Some(TokPred, tl)
  | 'n'::'o'::'t'::tl -> Some(TokNot, tl)
  | 'i'::'s'::'z'::'e'::'r'::'o'::tl -> Some(TokIsZero, tl)
  | 'p'::'l'::'u'::'s'::tl -> Some(TokPlus, tl)
  | _ -> raise Parse_exn

(* turn a string of code (like "(pred 0)" into a list of tokens (like [LParen, TokPred, TokZero, RParen]) *)
let rec scan (ls : char list) : token list = 
  match nextToken ls with 
  | None -> [] 
  | Some (tok, tl) -> tok :: scan tl 

(* Parser *)

(* nextTerm should return the next term from a list of tokens, along with the tokens thereafter
   - return None if the list of tokens is empty
   - throw an exception if the characters cannot be tokenized *)
let rec nextTerm (ts: token list) : (term * token list) option = 
  match ts with 
  | [] -> None
  | TokTrue::tl -> Some(True, tl)
  | TokFalse::tl -> Some(False, tl)
  | TokZero::tl -> Some(Zero, tl)
  | LParen::TokIf::tl -> 
    (match nextTerm tl with
    | Some(t1, tl1) -> 
      (match nextTerm tl1 with
      | Some(t2, tl2) ->
        (match nextTerm tl2 with
        | Some(t3, RParen::tl3) -> Some(If(t1, t2, t3), tl3)
        | _ -> raise Parse_exn)
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | LParen::TokSucc::tl -> 
    (match nextTerm tl with
    | Some(t1, RParen::tl1) -> Some(Succ(t1), tl1)
    | _ -> raise Parse_exn)
  | LParen::TokPred::tl -> 
    (match nextTerm tl with
    | Some(t1, RParen::tl1) -> Some(Pred(t1), tl1)
    | _ -> raise Parse_exn)
  | LParen::TokIsZero::tl -> 
    (match nextTerm tl with
    | Some(t1, RParen::tl1) -> Some(IsZero(t1), tl1)
    | _ -> raise Parse_exn)
  | LParen::TokAnd::tl -> 
    (match nextTerm tl with
    | Some(t1, tl1) -> 
      (match nextTerm tl1 with
      | Some(t2, RParen::tl2) -> Some(And(t1, t2), tl2)
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | LParen::TokOr::tl -> 
    (match nextTerm tl with
    | Some(t1, tl1) -> 
      (match nextTerm tl1 with
      | Some(t2, RParen::tl2) -> Some(Or(t1, t2), tl2)
      | _ -> raise Parse_exn)
    | None -> None)
  | LParen::TokNot::tl -> 
    (match nextTerm tl with
    | Some(t1, RParen::tl1) -> Some(Not(t1), tl1)
    | _ -> raise Parse_exn)
  | LParen::TokPlus::tl -> 
    (match nextTerm tl with
    | Some(t1, tl1) -> 
      (match nextTerm tl1 with
      | Some(t2, RParen::tl2) -> Some(Plus(t1, t2), tl2)
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | _ -> raise Parse_exn

(* turn a list of tokens (like [LParen ,TokPred, TokZero, RParen] into a term (like Pred 0) *)
let parse (tokens : token list) : term =
  match nextTerm tokens with
  | Some(t, []) -> t
  | _ -> raise Parse_exn

(* Small Step evaluator *)

(* Implement the small-step evaluation relation from class. 
   For And, Or and Not, you should be able to determine 
   appropriate rules by extrapolating from the If rules.
   If a term is not a normal form, take the next possible step
   - i.e., if t -> u, then step(t) should return Some(u)
   if a term is a normal form, return None *)
let rec small_step (t : term) : term option =
  match t with 
  | If(True, t2, _) -> Some(t2)
  | If(False, _, t3) -> Some(t3) 
  | If(t1, t2, t3) -> 
    (match small_step t1 with
    | Some(t1') -> Some(If(t1', t2, t3))
    | None -> None)
  | Succ(t1) ->
   (match small_step t1 with
    | Some(t1') -> Some(Succ(t1'))
    | None -> None)
  | Pred(Zero) -> Some(Zero)
  | Pred(Succ(t)) when is_num_val t -> Some(t)
  | Pred(t1) ->
    (match small_step t1 with
    | Some(t1') -> Some(Pred(t1'))
    | None -> None)
  | IsZero(Zero) -> Some(True) 
  | IsZero(Succ(t)) when is_num_val t -> Some(False) 
  | IsZero(t1) -> 
    (match small_step t1 with
    | Some(t1') -> Some(IsZero(t1'))
    | None -> None)
  | And(True, t2) -> Some(t2)
  | And(False, _) -> Some(False)
  | And(t1, t2) ->
    (match small_step t1 with
    | Some(t1') -> Some(And(t1', t2))
    | None -> None)
  | Or(True, _) -> Some(True)
  | Or(False, t2) -> Some(t2)
  | Or(t1, t2) -> 
    (match small_step t1 with
    | Some (t1') -> Some(Or(t1', t2))
    | None -> None)
  | Not(True) -> Some(False)
  | Not(False) -> Some(True)
  | Not(t1) -> 
    (match small_step t1 with
    | Some(t1') -> Some(Not(t1'))
    | None -> None)
  | Plus(Zero, t2) when is_num_val t2 -> Some(t2)
  | Plus(Succ(t1), t2) when is_num_val t1 -> 
    (match small_step t2 with
    | Some(t2') -> Some(Succ(Plus(t1, t2')))
    | None -> None)
  | Plus(t1, t2) -> 
    (match small_step t1 with
      | Some(t1') -> Some(Plus(t1', t2))
      | None -> 
        match small_step t2 with
        | Some(t2') -> Some(Plus(t1, t2'))
        | None -> None)
  | _ -> None 

(* Returns true if the term is a normal form, false otherwise. *)
let is_normal (t: term) : bool =
  match small_step t with
  | None -> true
  | _ -> false

(* Returns true if the term is stuck, false otherwise. *)
let is_stuck (t: term) : bool = is_normal t && not (is_val t)

(* Given t, return t' such that t ->* t' and t' is a normal form. *)
let rec multistep_full (t : term) : term =
  match is_normal t with
  | true -> t
  | false -> 
    match small_step t with
    | Some(t') -> multistep_full t'
    | None -> t

(* Returns true if a term steps to a value, and false otherwise. *)
let rec multisteps_to_value (t: term) : bool =
  match is_val t with
  | true -> true
  | false ->
    match small_step t with
    | Some(t') -> multisteps_to_value t'
    | None -> is_val t

(* Big Step evaluator *)

(* Now implement the big-step relation from class. 
   Again, return none if the program doesn't (big) step. 
   You should be able to infer the big step semantics of
   and, or, not and plus from the small-step ones. *)

let rec big_step (t : term) : term option =
  if is_val t then Some(t)
  else match t with
    | If(t1, t2, t3) ->
      (match big_step t1 with
        | Some(True) -> big_step t2
        | Some(False) -> big_step t3
        | _ -> None)
    | Succ(t1) -> 
      (match big_step t1 with
        | Some(t1) -> Some(Succ(t1))
        | _ -> None)
    | Pred(t1) ->
      (match big_step t1 with
        | Some(Zero) -> Some(Zero)
        | Some(Succ(t1)) -> Some(t1)
        | _ -> None)
    | IsZero(t1) -> 
      (match big_step t1 with
        | Some(Zero) -> Some(True)
        | Some(Succ(_)) -> Some(False)
        | _ -> None)
    | And(t1, t2) -> 
      (match big_step t1 with
        | Some(True) -> big_step t2
        | Some(False) -> Some(False)
        | _ -> None)
    | Or(t1, t2) -> 
      (match big_step t1 with
        | Some(True) -> Some(True)
        | Some(False) -> big_step t2
        | _ -> None)
    | Not(t1) -> 
      (match big_step t1 with
        | Some(True) -> Some(False)
        | Some(False) -> Some(True)
        | _ -> None)
    | Plus(t1, t2) ->
      (match big_step t1, big_step t2 with
      | Some(Zero), Some(t2') when is_num_val t2' -> Some(t2')
      | Some(Succ(t1)), Some(t2) when is_num_val t1 && is_num_val t2 -> Some(Succ(Plus(t1, t2)))
      | _ -> None)
    | _ -> None
