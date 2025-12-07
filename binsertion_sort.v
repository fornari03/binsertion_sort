Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.
(**
   A função [bsearch x l] retorna a posição [i] ($0 \leq i \leq |l|-1$) onde [x] deve ser inserido na lista ordenada [l]:
 *)

Require Import Recdef.
Require Import Wellfounded.

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
  - intros. rewrite <- teq1. rewrite skipn_length. simpl length. apply Nat.sub_lt.
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
 
(**
O lema original não está correto, como podemos ver no caso da lista vazia.
*)
 
Lemma neg_bsearch_valid_pos: ~forall l x, 0 <= bsearch x l < length l.
Proof.
intro h.
specialize (h [] 0) .
rewrite bsearch_equation in h.
simpl in h.
lia.
Qed.

(** 
nao sei qual seria a versao mais correta de se provar aqui, talvez a primeira pq na segunda teriamos que garantir Sorted l, mas n tenho ctz
*)
Lemma bsearch_valid_pos: forall l x, 0 <= bsearch x l <= length l.
Proof.
Admitted.

(**
Lemma bsearch_valid_pos: forall l x, (exists y, In y l /\ x <= y) -> 0 <= bsearch x l < length l.
Proof.
  intros. split.
   - lia.
   - rewrite bsearch_equation. destruct l. 
     * inversion H. inversion H0. contradiction.
     * destruct l. 
       + simpl. case_eq (x <=? n).
         -- auto.
         -- Admitted.
*)

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

(**
Lemas Auxiliares
*)
Lemma insert_at_app: forall (l: list nat) (n: nat) (x: nat),
  n <= length l ->
  insert_at n x l = (firstn n l) ++ (x :: skipn n l).
Proof.
  intros. induction n.
    - auto.
    - destruct l.
      * auto.
      * simpl. Admitted.

(**
que disse que dividimos a lista em 2 a partir do idx de x: os elementos menores que x e os maiores ou iguais a x
*)
Lemma bsearch_split_properties: forall l x,
  Sorted le l ->
  let k := bsearch x l in
  (forall y, In y (firstn k l) -> y < x) /\ 
  (forall z, In z (skipn k l) -> x <= z).
Proof.
  intros l x Hsort. functional induction (bsearch x l) using bsearch_ind.
    - split. simpl. intros. contradiction. simpl. intros. contradiction. 
    - split. simpl. intros. contradiction. simpl. intros. destruct H. apply Nat.leb_le in e0. lia. lia.
    - split. simpl. intros. apply Nat.leb_gt in e0. lia. intros. apply Nat.leb_gt in e0. destruct H.
    - split. simpl. intros. contradiction. 
      * simpl. intros. apply (f_equal (@length nat)) in e0. rewrite skipn_length in e0. assert (Hlen: length (h1 :: h2 :: tl) >= 2). { simpl. lia. } assert (Hdiv: length (h1 :: h2 :: tl) / 2 < length (h1 :: h2 :: tl)).
        + apply Nat.div_lt. lia. lia.
        + change (length []) with 0 in e0. lia.
    - Admitted.

Lemma sorted_join: forall l1 l2 x,
  Sorted le (l1 ++ l2) -> (* A lista original era ordenada *)
  (forall y, In y l1 -> y <= x) -> (* Tudo à esquerda é menor/igual a x *)
  (forall z, In z l2 -> x <= z) -> (* Tudo à direita é maior/igual a x *)
  Sorted le (l1 ++ x :: l2).
Proof.
Admitted.

Theorem binsert_correct: forall l x, Sorted le l -> Sorted le (binsert x l).
Proof.
  intros. unfold binsert. 
  pose proof (bsearch_split_properties l x H). destruct H0 as [H_le H_ge].
  assert (H_valid: bsearch x l <= length l). apply bsearch_valid_pos. rewrite insert_at_app; auto.
    - apply sorted_join. 
      * rewrite firstn_skipn. auto.
      * intros. apply Nat.lt_le_incl. apply H_le. auto.
      * intros. apply H_ge. auto.
Qed.
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
  - intros. rewrite <- teq1. rewrite skipn_length. apply Nat.sub_lt.
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

(** Precisamos que a lista esteja sortada pro binsert e binsert' funcionar *)
Lemma binsert_equiv_binsert': forall l x, Sorted le l -> binsert x l = binsert' x l.
Proof.
Admitted.

(**
 E portanto a correção de [binsert'] é imediata:
*)

Corollary binsert'_correct: forall l x, Sorted le l -> Sorted le (binsert' x l).
Proof.
  intros l x H. rewrite <- binsert_equiv_binsert'. apply binsert_correct. assumption.
  auto. (** Na minha IDE faltou um auto por algum motivo *)
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

Lemma insert_at_perm: forall n x l, Permutation (insert_at n x l) (x :: l).
Proof.
  induction n; simpl; intros.
  - (* Caso base: n = 0 *)
    apply Permutation_refl.
  - (* Passo indutivo *)
    destruct l as [| h tl].
    + (* Lista vazia *)
      simpl. apply Permutation_refl.
    + transitivity (h :: x :: tl).
      * constructor. apply IHn.
      * apply perm_swap.
Qed.

Lemma binsert_perm: forall x l, Permutation (binsert x l) (x :: l).
Proof.
  intros.
  unfold binsert.
  apply insert_at_perm.
Qed.

(**
   O teorema abaixo é o resultado principal a ser provado. Observe que pode ser conveniente dividir esta prova em outras provas menores. Isto significa que a formalização pode ficar mais simples e mais organizada com a inclusão de novos lemas.
 *)

Theorem binsertion_sort_correct: forall l, Sorted le (binsertion_sort l) /\ Permutation l (binsertion_sort l).
Proof.
  induction l.
  - (* Caso base: lista vazia *)
    simpl. split.
    + apply Sorted_nil.
    + apply Permutation_refl.
  - (* Passo indutivo *)
    simpl. destruct IHl as [H_sorted H_perm].
    split.
    + (* Parte da Ordenação (Sorted) *)
      apply binsert_correct. assumption.
    + (* Permutação *)
      transitivity (a :: binsertion_sort l).
      * constructor. assumption. (* Usa a hipótese de indução H_perm *)
      * apply Permutation_sym. apply binsert_perm.
Qed.
