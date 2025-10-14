Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

(**
   A função [bsearch x l] retorna a posição [i] ($0 \leq i \leq |l|-1$) onde [x] deve ser inserido na lista ordenada [l]:
 *)

Require Import Recdef.

Function bsearch x l {measure length l} :=
  match l with
  | [] => 0
  | [y] => if (x <=? y)
           then 0
           else 1
  | h1::h2::tl =>
      let len := length l in
      let mid := len / 2 in
      let l1 := firstn mid l in
      let l2 := skipn mid l in
      match l2 with
      | [] => 0
      | h2'::l2' => if (x <? h2')
                    then bsearch x l1
                    else
                      if x =? h2'
                      then mid
                      else mid + (bsearch x l2)
      end
  end.
Proof.
  - intros. rewrite firstn_length_le.
    + simpl length. apply Nat.div_lt.
      * lia.
      * auto.
    + simpl length. apply Nat.lt_le_incl. apply Nat.div_lt.
      * lia.
      * auto.
  - intros. rewrite <- teq1. rewrite length_skipn. simpl length. apply Nat.sub_lt.
    + apply Nat.lt_le_incl. apply Nat.div_lt.
      * lia.
      * auto.
    + apply Nat.div_str_pos. lia.
Defined.

(**
   Podemos fazer alguns testes com esta função:
 *)

Lemma test0: bsearch 1 [] = 0.
Proof.
  rewrite bsearch_equation. reflexivity.
Qed.

Lemma test1: bsearch 1 [0;2;3] = 1.
Proof.
  rewrite bsearch_equation. simpl. rewrite bsearch_equation. destruct (1 <=? 0) eqn: H.
  - inversion H.
  - reflexivity.
Qed.

Lemma test2: bsearch 2 [0;2;3] = 1.
Proof.
  rewrite bsearch_equation. simpl. reflexivity.
Qed.
  
Lemma test3: bsearch 2 [0;2;3;4] = 1.
Proof.
  rewrite bsearch_equation. simpl. rewrite bsearch_equation. simpl. reflexivity.
Qed.

Lemma test4: bsearch 3 [0;1;2;3;4;5] = 3.
Proof.
  rewrite bsearch_equation. simpl. reflexivity.
Qed.  

(**
Também podemos verificar que [bsearch x l] sempre retorna uma posição válida da lista [l]:
 *)

Lemma bsearch_valid_pos: forall l x, 0 <= bsearch x l < length l.
Proof.
  Admitted.

  
(**
A seguir, definiremos a função [insert_at i x l] que insere o elemento [x] na posição [i] da lista [l]:
 *)

Fixpoint insert_at i (x:nat) l :=
  match i with
  | 0 => x::l
  | S k => match l with
           | nil => [x]
           | h::tl => h::(insert_at k x tl)
           end
  end.

Eval compute in (insert_at 2 3 [1;2;3]).

(**
A função [binsert x l] a seguir insere o elemento x na posição retornada por [bsearch x l] de [l]:
 *)

Definition binsert x l :=
  let pos := bsearch x l in
  insert_at pos x l.

(**
 Agora podemos enunciar o teorema que caracteriza a correção da função [binsert], a saber, que [binsert x l] retorna uma lista ordenada, se [l] estiver ordenada: 
*)
(* begin hide *)
Require Import Sorted.
(* end hide *)

Theorem binsert_correct: forall l x, Sorted le l -> Sorted le (binsert x l).
Proof.
Admitted.    

(**
   Alternativamente, podemos construir uma única função que combina a execução de [bsearch] e [insert_at]. A função [binsert x l] a seguir, recebe o elemento [x] e a lista ordenada [l] como argumentos e retorna uma permutação ordenada da lista [x::l]: 
 *)

Function binsert' x l {measure length l} :=
  match l with
  | [] => [x]
  | [y] => if (x <=? y)
           then [x; y]
           else [y; x]
  | h1::h2::tl =>
      let len := length l in
      let mid := len / 2 in
      let l1 := firstn mid l in
      let l2 := skipn mid l in
      match l2 with
      | [] => l
      | h2'::l2' => if x =? h2'
                    then l1 ++ (x ::l2)
                    else
                      if x <? h2'
                      then binsert' x l1
                      else binsert' x l2
      end
  end.
Proof.
  - intros. rewrite firstn_length_le.
    + simpl length. apply Nat.div_lt; lia.
    + simpl length. apply Nat.lt_le_incl. apply Nat.div_lt; lia.
  - intros. rewrite <- teq1. rewrite length_skipn. apply Nat.sub_lt.
    + simpl length. apply Nat.lt_le_incl. apply Nat.div_lt; lia.
    + simpl length. apply Nat.div_str_pos. lia.
Defined.

Lemma teste0: (binsert' 2 [1;2;3]) = [1;2;2;3].
Proof.
  rewrite binsert'_equation. simpl. reflexivity.
Qed.

(**
As funções [binsert] e [binsert'] representam o mesmo algoritmo:
 *)

Lemma binsert_equiv_binsert': forall l x, binsert x l = binsert' x l.
Proof.
Admitted.

(**
 E portanto a correção de [binsert'] é imediata:
*)

Corollary binsert'_correct: forall l x, Sorted le l -> Sorted le (binsert' x l).
Proof.
  intros l x H. rewrite <- binsert_equiv_binsert'. apply binsert_correct. assumption.
Qed.

(**
O algoritmo principal é dado a seguir:
 *)

Fixpoint binsertion_sort (l: list nat) :=
  match l with
  | [] => []
  | h::tl => binsert h (binsertion_sort tl)
  end.

(* begin hide *)
Require Import Permutation.
(* end hide *)

(**
   O teorema abaixo é o resultado principal a ser provado. Observe que pode ser conveniente dividir esta prova em outras provas menores. Isto significa que a formalização pode ficar mais simples e mais organizada com a inclusão de novos lemas.
 *)

Theorem binsertion_sort_correct: forall l, Sorted le (binsertion_sort l) /\ Permutation l (binsertion_sort l).
Proof.
  Admitted.
