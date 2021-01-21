#use "reader.ml";;
open Reader;;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;
  
(* work on the tag parser starts here *)

let not_reserved x =
  not(List.mem x reserved_word_list);;

let rec list_to_pairs lst =
  match lst with
  | [] -> Nil
  | _ -> Pair(List.hd lst, list_to_pairs (List.tl lst));;

let rec pairs_to_list_sexpr pairs =
  match pairs with
  | Pair(exp, Nil) -> exp :: []
  | Pair(car, cdr) -> car :: (pairs_to_list_sexpr cdr)
  | _ -> raise X_syntax_error;;

let rec longest_var var_lst max =
  match var_lst with
  | [] -> max
  | _ -> let head = (List.hd var_lst) in
         let tail = (List.tl var_lst) in
         if max < String.length head
         then longest_var tail (String.length head)
         else longest_var tail max;;

let rec not_used_var n name =
  let name = "X" ^ name in
  match n with
  | 1 -> name
  | _ ->(not_used_var (n - 1) name);;

let rec rename_vars n name =
  match n with
  | 1 -> [name ^ (string_of_int n)]
  | _ -> (name ^ (string_of_int n)) :: (rename_vars (n - 1) name );;

let rec merge_lists_to_pairs lst1 lst2 =
  match lst1, lst2 with
  | [], [] -> Nil
  | _ -> Pair(Pair((List.hd lst1), Pair((List.hd lst2), Nil)), merge_lists_to_pairs (List.tl lst1) (List.tl lst2));;

let rec tag_parse = function
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | Number(x) -> Const(Sexpr(Number(x)))
  | String(x) -> Const(Sexpr(String(x)))
  | Symbol(x) when (not_reserved x) -> Var(x)
  | Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
  | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) ->
      If(tag_parse test, tag_parse dit, tag_parse dif)
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) ->
      If(tag_parse test, tag_parse dit, Const(Void))
  | Pair(Symbol("lambda"), Pair(Nil, body)) -> 
      LambdaSimple([], sequence body)
  | Pair(Symbol("lambda"), Pair(args, body)) when (is_proper_list args) -> 
      LambdaSimple(proper_pairs_to_list args, sequence body)
  | Pair(Symbol("lambda"), Pair(Symbol(arg), body)) ->
      LambdaOpt([], arg, sequence body)
  | Pair(Symbol("lambda"), Pair(args, body)) when not(is_proper_list args) ->
      LambdaOpt(improper_pairs_to_list args, get_opt_arg args, sequence body)
  | Pair(Symbol("quasiquote"), Pair(exp, Nil)) -> tag_parse (quasiquote_macro exp)
  | Pair(Symbol("cond"), exp) -> (cond_macro exp)
  | Pair(Symbol("let*"), exp) -> tag_parse (let_star_macro exp)
  | Pair(Symbol("letrec"), exp) -> tag_parse (letrec_macro exp)
  | Pair(Symbol("let"), exp) -> (let_macro exp)
  | Pair(Symbol("and"), exp) -> tag_parse (and_macro exp)
  | Pair(Symbol("begin"), exps) -> (sequence exps)
  | Pair(Symbol("set!"), Pair(set_var, Pair(set_val, Nil))) ->
      Set(tag_parse set_var, tag_parse set_val)
  | Pair(Symbol("pset!"), exp) -> tag_parse (pset_macro exp)
  | Pair(Symbol("or"), Nil) -> Const(Sexpr(Bool(false)))
  | Pair(Symbol("or"), Pair(exp, Nil)) -> tag_parse exp
  | Pair(Symbol("or"), exps) -> Or(pairs_to_list exps)
  | Pair(Symbol("define"), Pair(Pair(name, argl), expr)) -> 
      Def (tag_parse name, LambdaSimple(proper_pairs_to_list argl, sequence expr))
  | Pair(Symbol("define"), Pair(name, Pair(exp, Nil))) -> Def(tag_parse name, tag_parse exp)
  | Pair(exp, Nil) -> Applic(tag_parse exp, [])
  | Pair(exp, exps) -> Applic(tag_parse exp, pairs_to_list exps)
  | _ -> raise X_syntax_error

  and sequence exps =
    match exps with
    | Pair(exp, Nil) -> tag_parse exp
    | Nil -> Const(Void)
    | _ -> Seq(pairs_to_list exps)

  and pairs_to_list pairs =
    match pairs with
    | Pair(exp, Nil) -> (tag_parse exp) :: []
    | Pair(car, cdr) -> (tag_parse car) :: (pairs_to_list cdr)
    | _ -> raise X_syntax_error

  and proper_pairs_to_list pairs =
    match pairs with
    | Pair(Symbol(exp), Nil) -> exp :: []
    | Pair(Symbol(car), cdr) -> car :: (proper_pairs_to_list cdr)
    | _ -> raise X_syntax_error
  
  and improper_pairs_to_list pairs =
    match pairs with
    | Pair(Symbol(car), Symbol(cdr)) -> car :: []
    | Pair(Symbol(car), Pair(carcdr, cdr)) -> car :: (improper_pairs_to_list (Pair(carcdr, cdr)))
    | _ -> raise X_syntax_error

  and get_opt_arg pairs =
    match pairs with
    | Pair(Symbol(car), Symbol(cdr)) -> cdr
    | Pair(Symbol(car), Pair(carcdr, cdr)) -> (get_opt_arg (Pair(carcdr, cdr)))
    | _ -> raise X_syntax_error

  and is_proper_list lst =
    match lst with
    | Nil -> true
    | Pair(car, cdr) -> (is_proper_list cdr)
    | _ -> false

  (* macro expansions *)

  and quasiquote_macro exp =
    match exp with
    | Pair(Symbol("unquote"), Pair(exp, Nil)) -> exp
    | Pair(Symbol("unquote-splicing"), Pair(exp, Nil)) -> raise X_syntax_error
    | Nil -> Pair(Symbol("quote"), Pair(Nil, Nil))
    | Symbol(x) -> Pair(Symbol("quote"), Pair(Symbol(x), Nil))
    | Pair(Pair(Symbol("unquote-splicing"), Pair(exp, Nil)), cdr) ->
        Pair(Symbol("append"), Pair(exp, Pair((quasiquote_macro cdr), Nil)))
    | Pair(car, Pair(Symbol("unquote-splicing"), Pair(exp, Nil))) ->
        Pair(Symbol("cons"), Pair((quasiquote_macro car), Pair(exp, Nil)))
    | Pair(car, cdr) ->
        Pair(Symbol("cons"), Pair((quasiquote_macro car), Pair((quasiquote_macro cdr), Nil)))
    | _ -> exp

  and let_macro exp =
    match exp with
    | Pair(vars_and_vals, body) ->
        Applic(LambdaSimple(get_vars vars_and_vals, sequence body), (List.map tag_parse (get_vals vars_and_vals)))
    | _ -> raise X_syntax_error 

  and get_vars vars_and_vals =
    match vars_and_vals with
    | Pair(Pair(Symbol(v), exp), rest) -> List.append [v] (get_vars rest)
    | _ -> []

  and get_vals vars_and_vals =
    match vars_and_vals with
    | Pair(Pair(Symbol(v), Pair(exp, Nil)), rest) -> List.append [exp] (get_vals rest)
    | _ -> []

  and let_star_macro exp =
    match exp with
    | Pair(Nil, body) -> Pair(Symbol("let"), Pair(Nil, body))
    | Pair(Pair(Pair(Symbol(var), Pair(value, Nil)), Nil), body) ->
        Pair(Symbol("let"), Pair(Pair(Pair(Symbol(var), Pair(value, Nil)), Nil), body))
    | Pair(Pair(Pair(Symbol(var), Pair(value, Nil)), rest), body) -> 
        Pair(Symbol("let"), Pair(Pair(Pair(Symbol(var), Pair(value, Nil)), Nil), Pair(Pair(Symbol("let*"), Pair(rest, body)), Nil)))
    | _ -> raise X_syntax_error 

  and pset_macro exp =
    match exp with
    | Pair(Pair(pset_var, Pair(pset_val, Nil)), rest) ->
        let vars_list = (get_vars exp) in
        let len = List.length vars_list in
        let longest_name = (longest_var vars_list 0) in
        let new_name = (not_used_var longest_name "X") in
        let renamed_vars = List.map make_Symbol (rename_vars len new_name) in
        let vals_list = get_vals exp in
        let merged_pairs = merge_lists_to_pairs renamed_vars vals_list in
        let body = handle_pset_vars vars_list renamed_vars in
        Pair(Symbol("let"), Pair(merged_pairs, body)) 
    | _ -> raise X_syntax_error

  and handle_pset_vars vars_lst renamed_vars = 
    match vars_lst with
    | [] -> Nil
    | _ -> Pair(Pair(Symbol("set!"), Pair(Symbol(List.hd vars_lst), Pair((List.hd renamed_vars), Nil))), (handle_pset_vars (List.tl vars_lst) (List.tl renamed_vars)))

  and make_Symbol x = Symbol(x)

  and letrec_macro exp = 
     match exp with
    | Pair(args, body) ->
        let args_list = (letrec_handle_args args) in
        let body_list = (letrec_handle_body (pairs_to_list_sexpr args) body) in
        let last_let = Pair(Symbol("let"), Pair(Nil, body)) in
        let body = body_list @ [last_let] in
        let body = list_to_pairs body in
        Pair(Symbol("let"), Pair(args_list, body)) 
    | _ -> raise X_syntax_error

  and letrec_handle_args args =
    match args with
    | Pair(Pair(vars, Pair(vals, Nil)), rest) ->
        Pair(Pair(vars, Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), letrec_handle_args rest)
    | _ -> Nil

  and letrec_handle_body args body =
    List.map (fun pair -> match pair with
                          | Pair(vars, vals) -> Pair(Symbol("set!"), Pair(vars, vals))
                          | _ -> raise X_syntax_error) args

  and and_macro exp =
    match exp with
    | Nil -> Bool(true)
    | Pair(exp, Nil) -> exp
    | Pair(exp, exps) -> 
        Pair(Symbol("if"), Pair(exp, Pair(Pair(Symbol("and"), exps), Pair(Bool(false), Nil))))
    | _ -> raise X_syntax_error

    and cond_macro exp = 
    let rec handle_exprs exp =
      match exp with
      | Pair(Pair(expr, Pair(Symbol("=>"), exprf)), Nil) -> handle_arrow_1 expr exprf
      | Pair(Pair(expr, Pair(Symbol("=>"), exprf)), rest) -> handle_arrow_2 expr exprf rest
      | Pair(Pair(Symbol("else"), ribs), rest) -> Pair(Symbol("begin"), ribs)
      | Pair(Pair(rib, ribs), Nil) -> Pair(Symbol("if"), Pair(rib, Pair(Pair(Symbol("begin"), ribs), Nil)))
      | Pair(Pair(rib, ribs), rest) -> Pair(Symbol("if"), Pair(rib, Pair(Pair(Symbol("begin"), ribs), Pair(Pair(Symbol("cond"), rest), Nil))))
      | _ -> raise X_syntax_error
      
    in tag_parse (handle_exprs exp)

    and handle_arrow_1 expr exprf = 
      Pair(Symbol("let"), Pair(Pair(Pair(Symbol("value"), Pair(expr, Nil)), Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"),
        Pair(Nil, exprf)), Nil)), Nil)), (handle_if expr exprf Nil)))

    and handle_arrow_2 expr exprf rest = 
      Pair(Symbol("let"), Pair(Pair
      
      (Pair(Symbol("value"), Pair(expr, Nil)), Pair(Pair(Symbol("f"),
      Pair(Pair(Symbol("lambda"), Pair(Nil, exprf)), Nil)), Pair(Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"),
      Pair(Nil, Pair(Pair(Symbol("cond"), rest), Nil))), Nil)), Nil))), (handle_if expr exprf rest )))
      
    and handle_if expr exprf rest =  
      if rest = Nil
      then Pair(Pair(Symbol("if"), Pair(Symbol("value"),Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Nil))), Nil)
      else Pair(Pair(Symbol("if"), Pair(Symbol("value"),Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)),Pair(Pair(Symbol("rest"), Nil), Nil)))), Nil)

    ;;

let tag_parse_expressions sexpr = List.map tag_parse sexpr;;


  
end;; (* struct Tag_Parser *)

