
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | UL_POINT
    | UL_PAROUV
    | UL_PARFER
    | UL_IDENT of (
# 13 "Parser.mly"
       (string)
# 14 "Parser.ml"
  )
    | UL_FIN
    | UL_ENTIER of (
# 12 "Parser.mly"
       (int)
# 20 "Parser.ml"
  )
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState10
  | MenhirState7
  | MenhirState6
  | MenhirState1
  | MenhirState0

# 1 "Parser.mly"
  

(* Partie recopiee dans le fichier CaML genere. *)
(* Ouverture de modules exploites dans les actions *)
(* Declarations de types, de constantes, de fonctions, d'exceptions exploites dans les actions *)


# 52 "Parser.ml"

let rec _menhir_goto_s_expression_boucle : _menhir_env -> 'ttv_tail -> _menhir_state -> (unit) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _v : (unit) = 
# 41 "Parser.mly"
                                              ( (print_endline "S-expression : expression UL_FIN ") )
# 63 "Parser.ml"
         in
        _menhir_goto_expression_parenthesee _menhir_env _menhir_stack _menhir_s _v
    | MenhirState10 | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        let _v : (unit) = 
# 44 "Parser.mly"
                                                       ( (print_endline "S-expression : expression UL_FIN ") )
# 73 "Parser.ml"
         in
        _menhir_goto_s_expression_boucle _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        ();
        Printf.fprintf stderr "Internal failure -- please contact the parser generator's developers.\n%!";
        assert false

and _menhir_goto_expression_parenthesee : _menhir_env -> 'ttv_tail -> _menhir_state -> (unit) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | UL_PARFER ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, _) = _menhir_stack in
        let _v : (unit) = 
# 46 "Parser.mly"
                                                                     ( (print_endline "S-expression : expression UL_FIN ") )
# 96 "Parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _v : (unit) = 
# 36 "Parser.mly"
                                       ( (print_endline "S-expression : expression UL_FIN ") )
# 103 "Parser.ml"
         in
        _menhir_goto_s_expression _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (unit) = 
# 43 "Parser.mly"
                                      ( (print_endline "programme : S-expression UL_FIN ") )
# 118 "Parser.ml"
     in
    _menhir_goto_s_expression_boucle _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_s_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (unit) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | UL_ENTIER _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
        | UL_IDENT _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
        | UL_PAROUV ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState6
        | UL_POINT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState6 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | UL_ENTIER _v ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
            | UL_IDENT _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
            | UL_PAROUV ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState7
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7)
        | UL_PARFER ->
            _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState6
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6)
    | MenhirState7 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _, _) = _menhir_stack in
        let _v : (unit) = 
# 40 "Parser.mly"
                                                            ( (print_endline "S-expression : expression UL_FIN ") )
# 167 "Parser.ml"
         in
        _menhir_goto_expression_parenthesee _menhir_env _menhir_stack _menhir_s _v
    | MenhirState10 | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | UL_ENTIER _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
        | UL_IDENT _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
        | UL_PAROUV ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | UL_PARFER ->
            _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10)
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | UL_FIN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            let _v : (unit) = 
# 34 "Parser.mly"
                             ( (print_endline "programme : S-expression UL_FIN ") )
# 199 "Parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (unit)) = _v in
            Obj.magic _1
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState7 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | UL_ENTIER _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | UL_IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | UL_PAROUV ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | UL_PARFER ->
        _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState1

and _menhir_run2 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 13 "Parser.mly"
       (string)
# 257 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (unit) = 
# 37 "Parser.mly"
                           ( (print_endline "S-expression : expression UL_FIN ") )
# 265 "Parser.ml"
     in
    _menhir_goto_s_expression _menhir_env _menhir_stack _menhir_s _v

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 12 "Parser.mly"
       (int)
# 272 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (unit) = 
# 38 "Parser.mly"
                            ( (print_endline "S-expression : expression UL_FIN ") )
# 280 "Parser.ml"
     in
    _menhir_goto_s_expression _menhir_env _menhir_stack _menhir_s _v

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and scheme : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (unit) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | UL_ENTIER _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | UL_IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | UL_PAROUV ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

# 49 "Parser.mly"
  


# 323 "Parser.ml"

# 269 "<standard.mly>"
  

# 328 "Parser.ml"
