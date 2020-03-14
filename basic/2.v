Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(*
Вычисляет тип выражения (и выводит на консоль CoqIDE)

bool
day
bool -> bool

*)
Check true.
Check monday.
Check negb.

(*
Объявляется тип rgb и от него объявляется производный тип
Каждая строчка - это выражение-конструктор
primary - это конструктор, который принимает аргумент типа rgb
*)
Inductive rgb : Type :=
  | red
  | green
  | blue
  .

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb)
  .

(*
q - фиктивная переменная - она не используется и может быть заменена подстановочным символом "_"
*)
Definition monochrome (c : color) : bool :=
  match c with
  | black     => true
  | white     => true
  | primary q => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black       => false
  | white       => false
  | primary red => true
  | primary _   => false
  end.


Inductive bit : Type :=
  | B0
  | B1
  .

(* Тип-кортеж *)
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit)
  .

(* nybble *)
Check (bits B1 B0 B1 B0).

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _)     => false
  end.

Example all_zero_true:
	(all_zero (bits B0 B0 B0 B0)) = true
	.
Proof. simpl. reflexivity. Qed.

Example all_zero_false:
	(all_zero (bits B0 B0 B0 B1)) = false
	.
Proof. simpl. reflexivity. Qed.


(*
Это индуктивное определение целого неотрицательного числа, аналогично аксиомам Пеано
Начинаем с буквы O - это 0
И далее конструктор S - следующее за этим числом число
*)
Inductive nat : Type :=
  | O
  | S (n : nat).

(* Функция-предшественник *)
Definition pred (n : nat) : nat :=
  match n with
    | O    => O
    | S n' => n'
  end.

(* Fixpoint - рекурсивная функция
Данная функция смотрит, чётное число или нет
 *)
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(* Функция сложения двух аргументов типа nat *)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O    => m
    | S n' => S (plus n' m)
  end.

(* Функция умножения двух аргументов типа nat
Если n и m одного и того же типа, разрешена сокращённая нотация обоих аргументов *)
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O    => O
    | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult (S(S O)) (S(S O)) ) = (S(S(S(S O)))).
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _      => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

