type zero = private Dummy1
type _ succ = private Dummy2
type nil = private Dummy3
type 'a list = Nil | Cons of 'a * 'a list
(*'*('a, 'n) not important, we can write (_, _)*)
  type ('a, 'n) nlist = 
    | Nil : ('a, zero) nlist 
    | Cons : 'a * ('a, 'n) nlist -> ('a, 'n succ) nlist

(*Exercice 1*)
module Exo1 =
  struct
  (*map : ('a −> 'b) −> ('a, 'n) nlist −> ('b, 'n) nlist*)
  let rec map : type a b n. (a -> b) -> (a, n) nlist -> (b, n) nlist =
    fun f l ->
    match l with
    | Nil -> Nil
    | Cons (a, t) -> Cons (f a, map f t)

  (*snoc : 'a -> ('a, 'n) nlist −> ('a, 'n succ) nlist*)
  let rec snoc : type a n. a -> (a, n) nlist -> (a, n succ) nlist =
    fun a l ->
    match l with
    | Nil -> Cons (a, Nil)
    | Cons (x, t) -> Cons(x, snoc a t) 

  (*tail : ('a, 'n succ) nlist −> ('a, 'n) nlist*)
  let tail : type a n. (a, n succ) nlist -> (a, n) nlist =
    fun l ->
    match l with
    | Cons (_, t) -> t

  (*rev : ('a, 'n) nlist −> ('a, 'n) nlist *)
  let rec rev : type a n. (a, n) nlist -> (a, n) nlist =
    fun l ->
    match l with
    | Nil -> Nil 
    | Cons (x, t) -> snoc x (rev t)
end

(*Exercice 2*)
module Exo2 =
  struct
  (*insert : 'a -> ('a, 'n) nlist −> ('a, 'n succ) nlist *)
  let rec insert : type a n. a -> (a, n) nlist -> (a, n succ) nlist =
    fun x l ->
    match l with
    | Nil -> Cons (x, Nil) 
    | Cons (e, t) -> 
      if e < x then Cons (e, insert x t) else Cons (x, l)

  (*insertion_sort : ('a, 'n) nlist −> ('a, 'n succ) nlist *)
  let rec insertion_sort : type a n. (a, n) nlist -> (a, n) nlist =
    fun l ->
    match l with
    | Nil -> Nil
    | Cons (e, t) -> insert e (insertion_sort t)
end

(*Exercice 3*)
module Exo3 =
  struct
  type 'p hlist = 
    | Nil : nil hlist
    | Cons : 'a * 'p hlist -> ('a * 'p) hlist
  
  (*tail : ('a * 'p) hlist −> 'p hlist*)
  let tail : type a p. (a * p) hlist -> p hlist =
    fun l ->
    match l with
    | Cons (_, t) -> t

  (*add : (int * (int * 'p)) hlist -> (int * 'p) hlist *)
  let add : type p. (int * (int * p)) hlist -> (int * p) hlist =
    fun l ->
    match l with
    | Cons (x1, Cons(x2, t)) -> Cons(x1+x2, t)
end

module Exo4 =
  struct
  type 't expr = Entier : int -> int expr 
  | Booleen : bool -> bool expr
  | Plus : int expr * int expr -> int expr 
  | Egal : 't expr * 't expr -> bool expr

  (*eval : 't expr −> 't*)
  let rec eval : type t. t expr -> t =
    fun e ->
      match e with
      | Entier x -> x
      | Booleen x -> x
      | Plus (x1, x2) -> (eval x1) + (eval x2)
      | Egal (x1, x2) -> (eval x1) = (eval x2)


end
