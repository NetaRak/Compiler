#use "tag-parser.ml";;
open Tag_Parser;;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;	
                      
exception X_syntax_error;;

(* our code starts here *)

let contains x lst =
  List.mem x lst;;

let rec find_index_of name lst i = 
  match lst with
  | [] -> -1
  | car :: cdr -> (if (car = name) 
                  then i
                  else (find_index_of name cdr (i+1)));;

let rec find_env_index_and_var_index name env i = 
  match env with
  | [] -> (-1, -1)
  | car :: cdr -> (if (contains name car) 
                  then (i, (find_index_of name car 0))
                  else (find_env_index_and_var_index name cdr (i+1)));;

let rec lexical_addresses_handler env params exp =
  match exp with
  | Const(sexp) -> Const'(sexp)
  | Var(var_name) -> Var'(handle_var var_name params env)
  | If(test, dit, dif) ->
     If'(lexical_addresses_handler env params test, lexical_addresses_handler env params dit, lexical_addresses_handler env params dif)
  | Seq(exprs) -> Seq'(handle_expr_list exprs env params)
  | Set(expr, value) -> (match expr with
                        | Var(var_name) -> Set'(handle_var var_name params env, lexical_addresses_handler env params value)
                        | _ -> raise X_syntax_error)
  | Def(expr, value) -> (match expr with
                        | Var(var_name) -> Def'(handle_var var_name params env, lexical_addresses_handler env params value)
                        | _ -> raise X_syntax_error)
  | Or(exprs) -> Or'(handle_expr_list exprs env params)
  | LambdaSimple(args, body) -> LambdaSimple'(args, handle_lambda_simple env params args body)
  | LambdaOpt(args, opt, body) -> LambdaOpt'(args, opt, handle_lambda_opt env params args opt body)
  | Applic(expr, exprs) -> Applic'(lexical_addresses_handler env params expr, handle_expr_list exprs env params)

  and handle_var var_name params env =
    if (contains var_name params)
    then VarParam(var_name, (find_index_of var_name params 0))
    else (
      let var_address = (find_env_index_and_var_index var_name env 0) in
      match var_address with
      | (-1, -1) -> VarFree(var_name)
      | (env_index, var_index) -> VarBound(var_name, env_index, var_index)
    )

  and handle_expr_list exprs env params =
    List.map (lexical_addresses_handler env params) exprs

  and handle_lambda_simple env params args body =
    lexical_addresses_handler (params :: env) args body

  and handle_lambda_opt env params args opt body =
    let new_args = args @ [opt] in
    lexical_addresses_handler (params :: env) new_args body

  ;;

  let rec tail_calls_handler in_tp exp = 
    match exp with
    | Const'(expr) -> Const'(expr)
    | Var'(var_name) -> Var'(var_name)
    | If'(test, dit, dif) -> If'(tail_calls_handler false test, tail_calls_handler in_tp dit, tail_calls_handler in_tp dif)
    | Seq'(exprs) -> Seq'(handle_list_tc in_tp exprs)
    | Set'(vari, value) -> Set'(vari, tail_calls_handler false value)
    | Def'(vari, value) -> Def'(vari, tail_calls_handler false value)
    | Or'(exprs) -> Or'(handle_list_tc in_tp exprs)
    | LambdaSimple'(args, body) -> LambdaSimple'(args, tail_calls_handler true body)
    | LambdaOpt'(args, opt, body) -> LambdaOpt'(args, opt, tail_calls_handler true body)
    | Applic'(expr, exprs) -> if in_tp
                              then ApplicTP'(tail_calls_handler false expr, handle_list_tc false exprs)
                              else Applic'(tail_calls_handler false expr, handle_list_tc false exprs)
    | ApplicTP'(expr, exprs) -> ApplicTP'(expr, exprs)
    | Box'(expr) -> Box'(expr)
    | BoxGet'(expr) -> BoxGet'(expr)
    | BoxSet'(vari, expr) -> BoxSet'(vari, expr)

    and handle_list_tc in_tp exprs = 
      match exprs with
      | [] -> []
      | car :: [] -> (tail_calls_handler in_tp car) :: [] 
      | car :: cdr -> (tail_calls_handler false car) :: (handle_list_tc in_tp cdr)

    ;;

  let rec box_handler exp = 
    match exp with
    | Const'(expr) -> Const'(expr)
    | Var'(vari) -> (match vari with
                    | VarBound(name, major,minor) -> BoxGet'(vari)
                    | VarParam(name, i) -> BoxGet'(vari)
                    | _ -> Var'(vari))
    | If'(test, dit, dif) -> If'(box_handler test, box_handler dit, box_handler dif)
    | Seq'(exprs) -> Seq'(handle_list_boxing exprs)
    | Set'(vari, value) -> (match vari with
                            | VarBound(name, major, minor) -> BoxSet'(VarBound(name, major,minor), box_handler value)
                            | VarParam(name, i) -> BoxSet'(VarParam(name, i), box_handler value)
                            | _ -> Set'(vari, box_handler value))
    | Def'(vari, value) -> Def'(vari, box_handler value)
    | Or'(exprs) -> Or'(handle_list_boxing exprs)  
    | LambdaSimple'(args, body) -> (match List.length args with
                                  | 0 -> LambdaSimple'(args, box_handler body)
                                  | _ -> LambdaSimple'(args, (Seq'((handle_lambda_boxing args args) @ remove_seq (box_handler body)))))
    | LambdaOpt'(args, opt, body) -> LambdaOpt'(args, opt, (Seq'((handle_lambda_boxing (args @ [opt]) (args @ [opt])) @ [box_handler body])))                
    | Applic'(expr, exprs) -> Applic'(box_handler expr, handle_list_boxing exprs)
    | ApplicTP'(expr, exprs) -> ApplicTP'(box_handler expr, handle_list_boxing exprs)
    | Box'(expr) -> Box'(expr)
    | BoxGet'(expr) -> BoxGet'(expr)
    | BoxSet'(vari, expr) -> BoxSet'(vari, box_handler expr)

    and remove_seq exp = 
      match exp with
      | Seq'(x) -> x
      | _ -> [exp]

    and handle_list_boxing exprs = 
      List.map box_handler exprs

    and handle_lambda_boxing orig args =
      match args with
      | [] -> []
      | car :: [] -> (handle_top_lambda car orig)
      | car :: cdr -> (handle_top_lambda car orig) @ (handle_lambda_boxing orig cdr)

    and handle_top_lambda name args =
      [Set' (VarParam(name, find_index_of name args 0), Box'(VarParam(name, find_index_of name args 0)))]  

    ;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let annotate_lexical_addresses e = lexical_addresses_handler [] [] e;;

let annotate_tail_calls e = tail_calls_handler false e;;

let box_set e = box_handler e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
