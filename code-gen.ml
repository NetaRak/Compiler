#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

 (* global variables *)
let global_index : int ref = ref 0;;
let global_index_inc() = global_index := !global_index+1;;
let global_offset : int ref = ref 0;;
let global_offset_inc(off) = global_offset := !global_offset + off;;
let fvar_index : int ref = ref 32;;
let fvar_index_inc() = fvar_index := !fvar_index + 1;;
let global_consts_offset : (constant * int) list ref = ref [];;

  let rec remove_dups lst new_lst = 
    match lst with
    | [] -> new_lst
    | car :: cdr -> if List.mem car new_lst
                    then remove_dups cdr new_lst
                    else remove_dups cdr (new_lst @ [car]);;

  let contains x lst =
    List.mem x lst;;

  let rec fvar_not_contains name lst =
    match lst with
    | [] -> true
    | first :: rest -> match first with
                       | (fvar, index) -> if fvar = name
                                          then false
                                          else fvar_not_contains name rest

  let rec scan_ast_for_consts lst e =
    match e with
    | Const'(c) -> (match c with
                    | Sexpr(Pair(car, cdr)) ->  lst @ (scan_ast_for_consts lst (Const'(Sexpr(car)))) @ (scan_ast_for_consts lst (Const'(Sexpr(cdr)))) @ [c]
                    | Sexpr(Symbol(s)) -> lst @ (scan_ast_for_consts lst (Const'(Sexpr(String(s))))) @ [c]
                    | _ -> lst @ [c])
    | If'(test, dit, dif) -> (scan_ast_for_consts lst test) @ ((scan_ast_for_consts lst dit) @ (scan_ast_for_consts lst dif))
    | Seq'(exprs) -> List.flatten (List.map (scan_ast_for_consts lst) exprs)
    | Set'(vari, value) -> scan_ast_for_consts lst value
    | Def'(vari, value) -> scan_ast_for_consts lst value
    | Or'(exprs) -> List.flatten (List.map (scan_ast_for_consts lst) exprs)
    | LambdaSimple'(args, body) -> scan_ast_for_consts lst body
    | LambdaOpt'(args, opt, body) -> scan_ast_for_consts lst body
    | Applic'(expr, exprs) -> (scan_ast_for_consts lst expr) @ (List.flatten (List.map (scan_ast_for_consts lst) exprs))
    | ApplicTP'(expr, exprs) -> (scan_ast_for_consts lst expr) @ (List.flatten (List.map (scan_ast_for_consts lst) exprs))
    | BoxSet'(vari, expr) -> scan_ast_for_consts lst expr
    | _ -> lst;;

  let rec get_const_size c =
    match c with
    | Void -> 1
    | Sexpr(Nil) -> 1
    | Sexpr(Bool true) -> 2
    | Sexpr(Bool false) -> 2
    | Sexpr(Char(c)) -> 2
    | Sexpr(Number(Fraction(n,d))) -> 17
    | Sexpr(Number(Float f)) -> 9
    | Sexpr(String(s)) -> (String.length s) + 9
    | Sexpr(Symbol(s)) -> 9
    | Sexpr(Pair(a, b)) -> 17

    ;;

  let rec get_const_offset c consts_tbl =
    match consts_tbl with
    | [] -> -1
    | first :: rest -> match first with
                        | (const, offset) -> if c = const
                                             then offset
                                             else get_const_offset c rest

  let rec get_const_str c =
    match c with
    | Void -> "db T_VOID"
    | Sexpr(Nil) -> "db T_NIL"
    | Sexpr(Char(c)) -> "MAKE_LITERAL_CHAR " ^ string_of_int (Char.code c)
    | Sexpr(Bool(b)) -> if b = true then "db T_BOOL, 1" else "db T_BOOL, 0"
    | Sexpr(Number(Fraction(n,d))) -> "MAKE_LITERAL_RATIONAL(" ^ string_of_int n ^ ", " ^ string_of_int d ^ ")"
    | Sexpr(Number(Float f)) -> "MAKE_LITERAL_FLOAT(" ^ string_of_float f ^ ")"
    | Sexpr(String(s)) -> "MAKE_LITERAL_STRING " ^"\""^ s ^ "\" "
    | Sexpr(Symbol(s)) -> "MAKE_LITERAL_SYMBOL(const_tbl + " ^ string_of_int (get_const_offset (Sexpr(String(s))) !global_consts_offset) ^ ")"
    | Sexpr(Pair(car, cdr)) -> "MAKE_LITERAL_PAIR(const_tbl + " ^ string_of_int (get_const_offset (Sexpr(car)) !global_consts_offset) ^ ", const_tbl + " ^ string_of_int (get_const_offset (Sexpr(cdr)) !global_consts_offset) ^ ")"
  
    ;;

  let build_const c =
    let offset = !global_offset in 
    let const_offset = get_const_size c in
    let _ = global_offset_inc (const_offset) in
    global_consts_offset := !global_consts_offset @ [(c, offset)];
    (c, (offset, "\t" ^ get_const_str c));;

  let base_consts =
    [
      Void; Sexpr(Nil); Sexpr(Bool false); Sexpr(Bool true);
    ];;

let create_consts_tbl asts =
  let consts_tbl = List.flatten (List.map (scan_ast_for_consts []) asts) in
  let consts_tbl = base_consts @ consts_tbl in
  let consts_tbl = remove_dups consts_tbl [] in
  let consts_tbl = List.map build_const consts_tbl in
  consts_tbl;;

let rec address_in_const_table consts c = 
  match consts with 
  | first :: rest -> (match first with
                     | (Sexpr(sexp), (offset, _)) -> if (sexpr_eq c sexp)
                                                     then offset
                                                     else address_in_const_table rest c
                     | (Void, (offset, _)) -> address_in_const_table rest c)
                     
  | [] -> -1 ;;

  let base_fvars =
    [
      (* Type queries  *)
      ("boolean?", 0); ("flonum?", 1); ("rational?", 2);
      ("pair?", 3); ("null?", 4); ("char?", 5); ("string?", 6);
      ("procedure?", 7); ("symbol?", 8);
      (* String procedures *)
      ("string-length", 9); ("string-ref", 10); ("string-set!", 11);
      ("make-string", 12); ("symbol->string", 13);
      (* Type conversions *)
      ("char->integer", 14); ("integer->char", 15); ("exact->inexact", 16);
      (* Identity test *)
      ("eq?", 17);
      (* Arithmetic ops *)
      ("+", 18); ("*", 19); ("/", 20); ("=", 21); ("<", 22);
      (* Additional rational numebr ops *)
      ("numerator", 23); ("denominator", 24); ("gcd", 25);
      (* our functions *)
      ("car", 26); ("cdr", 27); ("cons", 28); ("set-car!", 29); ("set-cdr!", 30) ; ("apply" , 31)
    ];;

  let rec scan_ast_for_fvars lst e =
    match e with
    | Var'(VarFree(v)) -> handle_var_free v lst
    | If'(test, dit, dif) -> (scan_ast_for_fvars lst test) @ ((scan_ast_for_fvars lst dit) @ (scan_ast_for_fvars lst dif))
    | Seq'(exprs) -> List.flatten (List.map (scan_ast_for_fvars lst) exprs)
    | Set'(vari, value) -> scan_ast_for_fvars lst value
    | Def'(vari, value) -> scan_ast_for_fvars lst value
    | Or'(exprs) -> List.flatten (List.map (scan_ast_for_fvars lst) exprs)
    | LambdaSimple'(args, body) -> scan_ast_for_fvars lst body
    | LambdaOpt'(args, opt, body) -> scan_ast_for_fvars lst body
    | Applic'(expr, exprs) -> (scan_ast_for_fvars lst expr) @ (List.flatten (List.map (scan_ast_for_fvars lst) exprs))
    | ApplicTP'(expr, exprs) -> (scan_ast_for_fvars lst expr) @ (List.flatten (List.map (scan_ast_for_fvars lst) exprs))
    | BoxSet'(vari, expr) -> scan_ast_for_fvars lst expr
    | _ -> lst

    and handle_var_free v lst =
      let idx = !fvar_index in
      if (fvar_not_contains v lst)
      then (fvar_index_inc(); lst @ [(v, idx)])
      else lst;;


    let create_fvars_tbl asts =
      let fvars_tbl = List.flatten (List.map (scan_ast_for_fvars []) asts) in
      let fvars_tbl = base_fvars @ fvars_tbl in
      fvars_tbl;;

  let rec label_in_fvar_table name fvars =
    match fvars with
    | [] -> -1
    | first :: rest -> match first with
                       | (fvar, index) -> if fvar = name
                                          then index
                                          else label_in_fvar_table name rest

let rec code_generator consts fvars depth e =
  match e with
  | Const'(Sexpr(c)) -> "mov rax, const_tbl + " ^ string_of_int (address_in_const_table consts c) ^ "\n"
  | Var'(VarParam(_, minor)) -> "mov rax, qword[rbp + 8 * (4 + " ^ string_of_int minor ^ ")]\n"
  | Var'(VarBound(_, major, minor)) -> "mov rax, qword[rbp + 8 * 2]\n" ^
                                       "mov rax, qword[rax + 8 * " ^ string_of_int major ^ "]\n" ^
                                       "mov rax, qword[rax + 8 * " ^ string_of_int minor ^ "]\n"
  | Var'(VarFree(v)) -> "mov rax, qword[fvar_tbl + 8 * " ^ string_of_int (label_in_fvar_table v fvars) ^ "]\n"
  | Set'(v, epsi) -> handle_set v consts fvars depth epsi
  | Seq'(epsi_list) -> (String.concat "\n" (List.map (code_generator consts fvars depth) epsi_list)) ^ "\n"
  | Def'(v, epsi) -> handle_def v consts fvars depth epsi
  | Or'(epsi_list) -> handle_or epsi_list consts fvars depth 0
  | If'(q, t, epsi) -> handle_if q t epsi consts fvars depth
  | Box'(v) -> handle_box consts fvars depth v
  | BoxGet'(v) -> code_generator consts fvars depth (Var'(v)) ^ "\n" ^
                        "mov rax, qword[rax]\n"
  | BoxSet'(v, epsi) -> (code_generator consts fvars depth epsi) ^ "\n" ^
                              "push rax\n" ^ code_generator consts fvars depth (Var'(v)) ^ "\n" ^
                              "pop qword[rax]\nmov rax, SOB_VOID_ADDRESS"
  | LambdaSimple'(args, body) -> if depth = 0
                                 then handle_lambda_simple args body consts fvars depth
                                 else handle_nested_lambda_simple args body consts fvars depth
  | LambdaOpt'(args, opt, body) -> if depth = 0
                              then handle_lambda_opt args opt body consts fvars depth
                              else handle_nested_lambda_opt args opt body consts fvars depth
  | Applic'(proc, args) -> handle_applic proc args consts fvars depth
  | ApplicTP'(proc, args) -> handle_applic_tp proc args consts fvars depth
  | _ -> ";SOMTHING WENT WRONG"

  and handle_box consts fvars depth v =
    match v with
    | VarParam(name, minor) -> (code_generator consts fvars depth (Var'(v))) ^ "\n\t" ^ 
                               "MALLOC rbx, 8\n\tmov [rbx], rax\n\t" ^
                               "mov rax, rbx\n"
    | _ -> raise X_syntax_error

  and lambda_opt_body i num_of_args =
    "Lcode" ^ string_of_int i ^ ":\n\t" ^
    "push rbp\n\tmov rbp, rsp\n\t" ^
    (* adjust the stack for the opt args *)
    "mov rbx, [rbp + 8 * 3] ; rbx = num of args\n\t" ^
    "mov rcx, rbx\n\t" ^
    "sub rcx, " ^ string_of_int num_of_args ^ " ; rcx = num of opt args\n\t" ^
    "mov r12,rcx\n\t"^
    "mov r9, rbx\n\t" ^
    "add r9, 3 ; r9 = size of the stack without the magic\n\t" ^
    "mov r10, r9\n\t" ^
    "mov rbx, [rbp + 8 * r9] ; rbx hold the address of the top opt arg\n\t" ^
    "mov rdx, SOB_NIL_ADDRESS\n" ^
    "make_list" ^ string_of_int i ^ ":\n\t" ^
    "cmp rcx, 0\n\t" ^
    "je end_make_list" ^ string_of_int i ^ "\n\t" ^
    "MAKE_PAIR(rax, rbx, rdx) ; with pointers\n\t" ^
    "mov rdx, rax\n\t" ^
    "dec rcx\n\t" ^
    "dec r9\n\t" ^
    "mov rbx, [rbp + 8 * r9]\n\t" ^
    "jmp make_list" ^ string_of_int i ^ "\n" ^
    "end_make_list" ^ string_of_int i ^":\n\t" ^
    "mov rcx, [rbp + 8 * 3]\n\t" ^
    "sub rcx, " ^ string_of_int num_of_args ^ " ; rcx = num of opt args\n\t" ^
    "cmp rcx, 0\n\t" ^
    "je end_lambda_opt" ^ string_of_int i ^ "\n\t" ^
    "mov rbx, [rbp + 8 * 3]\n\t" ^
    "sub rbx, rcx\n\t" ^
    "inc rbx\n\t" ^
    "mov [rbp + 8 * 3], rbx ; rbx holds the new arg count, prev args + magic\n\t" ^
    "add rbx, 3 ; rbx = size of the new stack\n\t" ^
    "mov [rbp + 8 * rbx], rdx ; rdx hold the opt list\n" ^
    "shift_stack" ^ string_of_int i ^ ":\n\t" ^
    "cmp rbx, 0\n\t" ^
    "jl end_shift_stack" ^ string_of_int i ^ "\n\t" ^
    "mov rcx, [rbp + 8 * rbx]\n\t" ^
    "mov [rbp + 8 * r10], rcx\n\t" ^
    "dec r10\n\t" ^
    "dec rbx\n\t" ^
    "jmp shift_stack" ^ string_of_int i ^ "\n" ^
    "end_shift_stack" ^ string_of_int i ^ ":\n\t" ^
    "inc r10\n\t" ^
    "shl r10, 3\n\t" ^
    "add rsp, r10\n\t" ^
    "end_lambda_opt" ^ string_of_int i ^ ":\n\t"^
    "cmp r12,0\n"^
    "jne end_lambda_opt2_" ^ string_of_int i ^ "\n\t"^
    "mov r12,[rbp+ 8*3]\n"^
    "inc r12\n"^
    "mov [rbp+8*3],r12\n"^
    "add r12, 4\n"^
    "sub rbp,8
    mov r13,0
    fix_stack_loop" ^ string_of_int i ^ ":
      cmp r13,r12
      je done_fix"^ string_of_int i ^ "\n\t
      mov rdx,[rbp+8*(1+r13)]
      mov [rbp + 8* r13],rdx
      inc r13
      jmp fix_stack_loop" ^ string_of_int i ^"
    done_fix"^ string_of_int i ^":\n\t"^
      "mov qword[rbp+8*r12],SOB_NIL_ADDRESS
      sub rsp, 8\n"^
    "end_lambda_opt2_" ^ string_of_int i ^ ":\n\t"

  and handle_lambda_opt args opt body consts fvars depth =
    let i = !global_index in
    let _ = global_index_inc() in
    let num_of_args = List.length args in
    ";lambda opt\n" ^
    "MALLOC rbx, 8\n" ^
    "MAKE_CLOSURE(rax, rbx, Lcode" ^ string_of_int i ^ ")\n" ^
    "jmp Lcont" ^ string_of_int i ^ "\n" ^

    (lambda_opt_body i num_of_args) ^

    "mov rbp, rsp\n\t" ^
    (code_generator consts fvars (depth + 1) body) ^ "\n\t" ^
    "leave\n\tret\nLcont" ^ string_of_int i ^ ":\n"

  and handle_nested_lambda_opt args opt body consts fvars depth =
    let i = !global_index in
    let _ = global_index_inc() in
    let num_of_args = List.length args in
    ";nested_lambda_opt" ^ string_of_int i ^ ":\n" ^
    "mov rbx, 8 * " ^ string_of_int depth ^ "\n" ^ (* allocating the ExtEnv *)
    "MALLOC rbx, rbx\n" ^
    "mov rdx, [rbp + 8 * 2]\n" ^ (* rdx points to the prev env *)
    "mov rcx, " ^ (string_of_int depth) ^ "\n" ^
    "mov rdi, 0\n" ^
    "copy_pointers" ^ string_of_int i ^ ":\n\t" ^
    "cmp rcx, rdi\n\tje end_copy" ^ string_of_int i ^ "\n\t" ^
    "mov rax, [rdx + 8 * rdi]\n\t" ^ (* rax = prev env at rdi *)
    "inc rdi\n\t" ^
    "mov [rbx + 8 * rdi], rax\n\t" ^
    "jmp copy_pointers" ^ string_of_int i ^ "\n" ^
    "end_copy" ^ string_of_int i ^ ":\n\t" ^
    "mov rdx, [rbp + 8 * 3]\n" ^
    "shl rdx, 3\n\t" ^
    "MALLOC rdx, rdx\n\t" ^ (* allocate ExtEnv[0] to point to args vector *)
    "mov rdi, 0\n\t" ^
    "mov rcx, [rbp + 8 * 3]\n" ^
    "copy_args" ^ string_of_int i ^ ":\n\t" ^
    "cmp rdi, rcx\n\t" ^
    "je end_copy_args" ^ string_of_int i ^ "\n\t" ^
    "mov rax, [rbp + 8 * (4 + rdi)]\n\t" ^ (* points to arg * rdi *)
    "mov [rdx + 8 * rdi], rax\n\t" ^
    "inc rdi\n\t" ^
    "jmp copy_args" ^ string_of_int i ^ "\n" ^
    "end_copy_args" ^ string_of_int i ^ ":\n\t" ^
    "mov [rbx], rdx\n\t" ^
    "MAKE_CLOSURE(rax, rbx, Lcode" ^ string_of_int i ^ ")\n\t" ^
    "jmp Lcont" ^ string_of_int i ^ "\n" ^

    (lambda_opt_body i num_of_args) ^

    "mov rbp, rsp\n\t" ^
    (code_generator consts fvars (depth + 1) body) ^ "\n\t" ^
    "leave\n\tret\nLcont" ^ string_of_int i ^ ":\n"

  and handle_lambda_simple args body consts fvars depth =
    let i = !global_index in
    let _ = global_index_inc() in
    "MALLOC rbx, 8\n" ^
    "MAKE_CLOSURE(rax, rbx, Lcode" ^ string_of_int i ^ ")\n" ^
    "jmp Lcont" ^ string_of_int i ^ "\n" ^
    "Lcode" ^ string_of_int i ^ ":\n\t" ^
    "push rbp\n\tmov rbp, rsp\n\t" ^
    (code_generator consts fvars (depth + 1) body) ^ "\n\t" ^
    "leave\n\tret\nLcont" ^ string_of_int i ^ ":\n"

  and handle_nested_lambda_simple args body consts fvars depth =
    let i = !global_index in
    let _ = global_index_inc() in
    "nested_lambda" ^ string_of_int i ^ ":\n" ^
    "mov rbx, 8 * " ^ string_of_int depth ^ "\n" ^ (* allocating the ExtEnv *)
    "MALLOC rbx, rbx\n" ^
    "mov rdx, [rbp + 8 * 2]\n" ^ (* rdx points to the prev env *)
    "mov rcx, " ^ (string_of_int depth) ^ "\n" ^
    "mov rdi, 0\n" ^
    "copy_pointers" ^ string_of_int i ^ ":\n\t" ^
    "cmp rcx, rdi\n\tje end_copy" ^ string_of_int i ^ "\n\t" ^
    "mov rax, [rdx + 8 * rdi]\n\t" ^ (* rax = prev env at rdi *)
    "inc rdi\n\t" ^
    "mov [rbx + 8 * rdi], rax\n\t" ^
    "jmp copy_pointers" ^ string_of_int i ^ "\n" ^
    "end_copy" ^ string_of_int i ^ ":\n\t" ^
    "mov rdx, [rbp + 8 * 3]\n" ^
    "shl rdx, 3\n\t" ^
    "MALLOC rdx, rdx\n\t" ^ (* allocate ExtEnv[0] to point to args vector *)
    "mov rdi, 0\n\t" ^
    "mov rcx, [rbp + 8 * 3]\n" ^
    "copy_args" ^ string_of_int i ^ ":\n\t" ^
    "cmp rdi, rcx\n\t" ^
    "je end_copy_args" ^ string_of_int i ^ "\n\t" ^
    "mov rax, [rbp + 8 * (4 + rdi)]\n\t" ^ (* points to arg * rdi *)
    "mov [rdx + 8 * rdi], rax\n\t" ^
    "inc rdi\n\t" ^
    "jmp copy_args" ^ string_of_int i ^ "\n" ^
    "end_copy_args" ^ string_of_int i ^ ":\n\t" ^
    "mov [rbx], rdx\n\t" ^
    "MAKE_CLOSURE(rax, rbx, Lcode" ^ string_of_int i ^ ")\n\t" ^
    "jmp Lcont" ^ string_of_int i ^ "\n" ^
    "Lcode" ^ string_of_int i ^ ":\n\t" ^
    "push rbp\n\tmov rbp, rsp\n\t" ^
    (code_generator consts fvars (depth + 1) body) ^ "\n\t" ^
    "leave\n\tret\nLcont" ^ string_of_int i ^ ":\n"

  and handle_applic proc args consts fvars depth =
    let i = !global_index in
    let _ = global_index_inc() in 
    let args = List.rev args in
    let length = List.length args in
    ";applic:\n" ^
    "push SOB_NIL_ADDRESS ; push magic\n" ^
    (handle_applic_args args consts fvars depth) ^ 
    "push " ^ string_of_int length ^ "\n" ^
    (code_generator consts fvars depth proc) ^ "\n" ^
    (* verify that rax has type closure
    push rax -> env
    call rax -> code *)
    "push qword[rax + 1]\n" ^
    "call [rax + 9]\n" ^
    "check" ^ string_of_int i ^ ":\n" ^
    "add rsp, 8*1 ; pop env\n" ^
    "pop rbx ; pop arg count\n" ^
    "shl rbx, 3 ; rbx = rbx * 8\n" ^
    "add rsp, rbx; pop args\n" ^
    "add rsp, 8 ; pop magic" 

  and handle_applic_tp proc args consts fvars depth =
    let args = List.rev args in
    let length = List.length args in
    "push SOB_NIL_ADDRESS ; push magic\n" ^
    (handle_applic_args args consts fvars depth) ^ 
    "push " ^ string_of_int length ^ "\n" ^
    (code_generator consts fvars depth proc) ^ "\n" ^
    ";applicTP:\n" ^
    "push qword[rax + 1]\n" ^
    "push qword [rbp + 8 * 1] ;old ret addr\n" ^
    (* fix the stack *)
    "mov r10, [rbp]\n" ^
    "push rax\n" ^
    "mov rax, [rbp + 8 * 3]\n" ^
    "add rax, 5 ; add magic and old fram\n" ^
    "mov rbx, rax\n" ^
    "%assign i 1\n" ^
    "%rep " ^ string_of_int (length + 4) ^ "\n" ^
      "dec rax\n" ^
      "push qword[rbp - WORD_SIZE * i]\n" ^
      "pop qword[rbp + WORD_SIZE * rax]\n" ^
    "%assign i i+1\n" ^
    "%endrep\n" ^
    "pop rax\n" ^
    "mov rbp, r10\n" ^
    "shl rbx, 3\n" ^
    "add rsp, rbx\n" ^
    "jmp [rax + 9]\n"

  and handle_applic_args args consts fvars depth = 
    match args with
    | [] -> "\n"
    | (first :: rest) -> (code_generator consts fvars depth first) ^ "\n" ^
                          "push rax\n" ^  handle_applic_args rest consts fvars depth


  and handle_set v consts fvars depth epsi=
    match v with
    | VarParam(_, minor) -> (code_generator consts fvars depth epsi) ^ "\n" ^
                            "mov qword[rbp + 8 * (4 + " ^ string_of_int minor ^ ")], rax\n" ^
                            "mov rax, SOB_VOID_ADDRESS\n"
    | VarBound(_, major, minor) -> (code_generator consts fvars depth epsi) ^ "\n" ^
                                    "mov rbx, qword[rbp + 8 * 2]\n" ^
                                    "mov rbx, qword[rax + 8 * " ^ string_of_int major ^ "]\n" ^
                                    "mov qword[rbx + 8 * " ^ string_of_int minor ^ "], rax\n" ^
                                    "mov rax, SOB_VOID_ADDRESS\n"
    | VarFree(v) -> (code_generator consts fvars depth epsi) ^ "\n" ^
                     "mov qword[fvar_tbl + 8 * " ^ string_of_int (label_in_fvar_table v fvars) ^ "], rax\n" ^
                     "mov rax, SOB_VOID_ADDRESS\n"

  and handle_def v consts fvars depth epsi = 
    let _ = scan_ast_for_fvars fvars (Var'(v)) in
    match v with
    | VarFree(v) -> (code_generator consts fvars depth epsi) ^ "\n" ^
                    "mov qword[fvar_tbl + 8 * " ^ string_of_int (label_in_fvar_table v fvars) ^ "], rax\n" ^
                    "mov rax, SOB_VOID_ADDRESS\n"
    | _ -> raise X_syntax_error
 
    and handle_or epsi_list consts fvars depth count = 
      let count = count + 1 in
      let i = !global_index in
      let _ = global_index_inc() in
      match epsi_list with
      | [] -> loop_over_Lexit i count
      | car :: cdr -> (code_generator consts fvars depth car) ^
                      "\ncmp rax, SOB_FALSE_ADDRESS\njne Lexit" ^ (string_of_int i) ^ "\n" ^
                      (handle_or cdr consts fvars depth count)

    and loop_over_Lexit i count = 
      match count with
      | 0 -> "\n"
      | _ -> "\nLexit" ^ string_of_int i ^ ":" ^ (loop_over_Lexit (i-1) (count-1))

    and handle_if q t epsi consts fvars depth =
      let i = !global_index in
      let _ = global_index_inc() in
      (code_generator consts fvars depth q) ^
      "\ncmp rax, SOB_FALSE_ADDRESS\nje Lelse" ^ string_of_int i ^ "\n" ^
      (code_generator consts fvars depth t) ^
      "\njmp Lexit" ^ string_of_int i ^ "\nLelse"  ^ string_of_int i ^ ":\n" ^
      "mov rax, SOB_VOID_ADDRESS\n" ^
      (code_generator consts fvars depth epsi) ^
      "\nLexit" ^ string_of_int i ^ ":\n"

  ;;


module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = create_consts_tbl asts;;
  let make_fvars_tbl asts = create_fvars_tbl asts;;
  let generate consts fvars e = code_generator consts fvars 0 e;;

end;;