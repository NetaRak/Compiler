
#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

  (* Start of our code *)

let make_paired nt_left nt_right nt = 
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

let nt_whitespaces = star(const (fun ch -> ch <= ' '));;

let tok_true = word_ci "#t";;
let tok_false = word_ci "#f";;

let quote = (word_ci "'");;
let quasiquote = (word_ci "`");;
let unquote_splicing = (word_ci ",@");;
let unquote = (word_ci ",");;

let meta_return = pack (word "\\r") (fun _ -> char_of_int 13);;
let meta_newline = pack (word "\\n") (fun _ -> char_of_int 10);;
let meta_tab = pack (word "\\t") (fun _ -> char_of_int 9);;
let meta_page = pack (word "\\f") (fun _ -> char_of_int 12);;
let meta_backslash = pack (word "\\\\") (fun _ -> char_of_int 92);;
let meta_double_quote = pack (word "\\\"") (fun _ -> char_of_int 34);;

let tok_lparen = (char '(') ;;
let tok_rparen = (char ')') ;;
let tok_dot = (char '.') ;;
let nt_sign = disj(char '-')(char '+') ;;
let nt_digits = plus(range_ci '0' '9') ;;
let nt_e = (word_ci "e") ;;

let tok_visible_simple_char = const (fun ch -> ch > ' ');;

let rec gcd a b =
  if b = 0 then a else gcd b (a mod b);;

let symbol_char_no_dot = disj_list [(char '!'); (char '$'); (char '^'); (char '*'); (char '-');
  (char '_'); (char '='); (char '+'); (char '<'); (char '>');
  (char '?'); (char '/'); (char ':'); (range_ci 'a' 'z'); (range_ci 'A' 'Z'); (range_ci '0' '9')];;

let named_char_list = disj_list [(word_ci "newline"); (word_ci "nul"); (word_ci "page");
  (word_ci "return"); (word_ci "space"); (word_ci "tab"); ];;

let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;

let nt_any exp = const (fun c -> true) exp;;

let nt_line_comments = 
  let nt_semicolon = char ';' in
  let nt_end_comment_line = star(const (fun ch -> (ch != '\n') && (ch != (char_of_int 4)))) in
  let nt_comments = caten nt_semicolon (star (diff nt_any nt_end_comment_line)) in
  let nt_comments = caten nt_comments nt_end_comment_line in
  let nt_comments = pack nt_comments (fun (a, b) -> Nil) in
  make_spaced nt_comments;;

let nt_line_comments = pack (star nt_line_comments) (fun _ -> Nil);;

let rec sexprs exp = del_spaces_and_comments(disj_list [number_parser; nt_boolean; char_parser; string_parser; 
                               pair_parser; quote_like_parser; symbol_parser]) exp
          
(* sexpr comments *)

and sexpr_comment exp =
  let nt = (pack (caten (caten (word "#;") (star sexpr_comment)) sexprs) (fun _ -> Nil)) in
  nt exp

and make_multiple_comments nt =
  let disj_comments = disj_list [sexpr_comment; nt_line_comments; (pack nt_whitespaces (fun _ -> Nil))] in
  let packed = pack (make_spaced disj_comments) (fun _ -> Nil) in
  packed nt

and del_spaces_and_comments nt = make_paired make_multiple_comments make_multiple_comments nt

(* Nil parser *)

and nil_parser exp =
  let nt_nil = pack (caten tok_lparen tok_rparen) (fun (lparen, rparen) -> Nil) in
  (del_spaces_and_comments nt_nil) exp

(* number parser *)

and number_parser exp = 

  (* natural number *)
  let nt_number = pack nt_digits (fun digs -> int_of_string(list_to_string digs)) in
  let nt_number = caten (maybe nt_sign) nt_number in
  let nt_number =  pack nt_number (fun (sign, dig) ->
    match sign with 
    | Some('+') -> Fraction (dig, 1)
    | Some('-') -> Fraction (((-1) * dig), 1)
    | None -> Fraction (dig, 1)
    | _ -> raise X_no_match) in

  (* fraction *)
  let digs_with_slash = caten nt_digits (char '/') in
  let nt_frac = pack digs_with_slash (fun (digs, slash) -> int_of_string(list_to_string digs)) in
  let nt_denomi = pack nt_digits (fun (digs) -> int_of_string(list_to_string digs)) in
  let nt_frac = (caten (maybe nt_sign) (caten nt_frac nt_denomi)) in
  let nt_frac = pack nt_frac (fun (sign, (numerator, denominator)) ->
  let nt_gcd = gcd numerator denominator in
    match sign with 
    | Some('+') -> Fraction (numerator/nt_gcd, denominator/nt_gcd)
    | Some('-') -> Fraction (((-1) * numerator/nt_gcd), denominator/nt_gcd)
    | None -> Fraction (numerator/nt_gcd, denominator/nt_gcd)
    | _ -> raise X_no_match) in

  (* floating point *)
  let digs_with_dot = caten nt_digits (char '.') in
  let nt_float = pack digs_with_dot (fun (digs, dot) -> digs @ [dot]) in
  let nt_float = caten nt_float nt_digits in
  let nt_float = pack nt_float (fun (digs_with_dot, rest_of_digs) -> digs_with_dot @ rest_of_digs) in
  let nt_float = pack nt_float (fun flt -> float_of_string(list_to_string flt)) in
  let nt_float = caten (maybe nt_sign) nt_float in
  let nt_float =  pack nt_float (fun (sign, flt) ->
    match sign with 
    | Some('+') -> Float flt
    | Some('-') -> Float ((float_of_int(-1)) *. flt)
    | None -> Float flt
    | _ -> raise X_no_match) in

  (* scientific notation *)
  let nt_sci_int = pack nt_digits (fun digs -> float_of_string(list_to_string digs)) in
  let nt_sci_int = (caten (maybe nt_sign) nt_sci_int) in
  let nt_sci_int =  pack nt_sci_int (fun (sign, dig) ->
  match sign with 
  | Some('+') -> dig
  | Some('-') -> ((float_of_int (-1)) *. dig)
  | None -> dig
  | _ -> raise X_no_match) in

  let digs_with_dot = caten nt_digits (char '.') in
  let nt_sci_float = pack digs_with_dot (fun (digs, dot) -> digs @ [dot]) in
  let nt_sci_float = caten nt_sci_float nt_digits in
  let nt_sci_float = pack nt_sci_float (fun (digs_with_dot, rest_of_digs) -> digs_with_dot @ rest_of_digs) in
  let nt_sci_float = pack nt_sci_float (fun flt -> float_of_string(list_to_string flt)) in
  let nt_sci_float = caten (maybe nt_sign) nt_sci_float in
  let nt_sci_float =  pack nt_sci_float (fun (sign, flt) ->
    match sign with 
    | Some('+') -> flt
    | Some('-') -> ((float_of_int(-1)) *. flt)
    | None -> flt
    | _ -> raise X_no_match) in

  let sci_num = disj nt_sci_float nt_sci_int  in
  let sci_num = caten sci_num (caten nt_e nt_sci_int) in
  let sci_num = pack sci_num (fun (f, (e, i)) -> f*.(10.**i)) in
  let sci_num = pack sci_num (fun num -> (Float num)) in

  let numbers = pack (not_followed_by (disj_list [sci_num; nt_float; nt_frac; nt_number]) symbol_char_no_dot) (fun n -> Number(n)) in
  (del_spaces_and_comments numbers) exp

(* string parser *)

and string_parser exp =
  let string_literal_char = const (fun ch -> ch != '\"' && ch != '\\') in
  let string_meta_char = disj_list [meta_return; meta_newline; meta_tab; meta_page; meta_backslash;
                                    meta_double_quote] in
  let string_char = disj string_literal_char string_meta_char in
  let string_char = star string_char in
  let string_char = make_paired (char '\"') (char '\"') string_char in
  let string_char = pack string_char (fun e -> String (list_to_string e)) in
  (del_spaces_and_comments string_char) exp

(* boolean parser *)

and nt_boolean exp =
  let nt = disj tok_true tok_false in
  let nt = pack nt (fun (e) -> match (String.lowercase_ascii (list_to_string e)) with
      | "#f" -> Bool(false)
      | "#t" -> Bool(true)
      | _ -> raise X_no_match) in
  (del_spaces_and_comments nt) exp

(* symbol parser *)

and symbol_parser exp =
  let symbol_char = disj (char '.') symbol_char_no_dot in
  let symbol_char_no_dot = pack symbol_char_no_dot (fun e -> [e]) in
  let symbol_char = pack (caten symbol_char (plus symbol_char)) (fun (e, es) -> (e :: es)) in
  let symbol = disj symbol_char symbol_char_no_dot in
  let symbol = pack symbol (fun s -> Symbol (String.lowercase_ascii (list_to_string s))) in
  (del_spaces_and_comments symbol) exp

(* char parser *)

  and char_parser exp = 
    let visible_simple_char = pack tok_visible_simple_char (fun e -> [e]) in
    let char_nt = pack (caten (word_ci "#\\") (disj named_char_list visible_simple_char)) (fun (prefix, rest) ->
    match ((list_to_string prefix), String.lowercase_ascii(list_to_string rest)) with
      | ("#\\", "newline") -> Char '\n'
      | ("#\\", "nul") -> Char '\000'
      | ("#\\", "page") -> Char '\012'
      | ("#\\", "return") -> Char '\r'
      | ("#\\", "space") -> Char ' '
      | ("#\\", "tab") -> Char '\t'
      | ("#\\", c) -> Char (list_to_string rest).[0]
      | (_, _) -> raise X_no_match) in
    (del_spaces_and_comments char_nt) exp

  (* pair parser *)

    and pair_parser exp =
    let tok_lparen = make_paired make_multiple_comments make_multiple_comments tok_lparen in
    let nt_list = make_paired tok_lparen tok_rparen (star sexprs) in
    let nt_list = pack nt_list (fun exps -> List.fold_left (fun a b -> Pair(b, a)) Nil (List.rev exps)) in
   
    let nt_dotted_list = pack (caten (plus sexprs) (char '.')) (fun (sexp, dot) -> sexp) in
    let nt_dotted_list = make_paired tok_lparen tok_rparen (caten nt_dotted_list sexprs) in
    let nt_dotted_list = pack nt_dotted_list (fun (ls, exp) -> List.fold_left (fun a b -> Pair(b, a)) exp (List.rev ls)) in
    (del_spaces_and_comments (not_followed_by (disj nt_list nt_dotted_list) symbol_char_no_dot)) exp

    (* quote_like_parser *)

  and quote_like_parser exp =
    let nt_quote = pack (caten quote sexprs) (fun (sign, sexp) -> Pair(Symbol("quote"), Pair(sexp, Nil))) in
    let nt_quasiquote = pack (caten quasiquote sexprs) (fun (sign, sexp) -> Pair(Symbol("quasiquote"), Pair(sexp, Nil))) in
    let nt_unquote_splicing = pack (caten unquote_splicing sexprs) (fun (sign, sexp) -> Pair(Symbol("unquote-splicing"), Pair(sexp, Nil))) in
    let nt_unquote = pack (caten unquote sexprs) (fun (sign, sexp) -> Pair(Symbol("unquote"), Pair(sexp, Nil))) in
    (del_spaces_and_comments (disj nt_quote (disj nt_quasiquote (disj nt_unquote_splicing nt_unquote)))) exp;;

(* End of our code *)

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let read_sexprs string = 
      match ((star sexprs) (string_to_list string)) with
      | (sexps, []) -> sexps
      | _ -> raise X_no_match;;

  
end;; (* struct Reader *)
