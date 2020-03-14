(* Стандартная библиотека также определяет тип nat *)
Check 2.
(* 2: nat *)

Check S(S(O)).
(* 2: nat - такого на нестандартном типе nat нет *)


Example test_mult22: (mult (S(S O)) (S(S O)) ) = (S(S(S(S O)))).
Proof. simpl. reflexivity. Qed.
Example test_mult33: (mult 3 3 ) = 9.
Proof. simpl. reflexivity. Qed.

(* simpl - упростить выражение; reflexivity проверить на равенство
Т.к. reflexivity может само упростить выражение, 
то simpl не нужен и полезен только при отладке,
чтобы видеть состояние после упрощения

0 + n = n он доказать может, а вот симметрично n + 0 = n - нет
 *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl. reflexivity. Qed.

(* n = m ->
это условие на переменные n и m
*)
Theorem plus_id_example: forall n m: nat, n = m -> n + n = m + m.
Proof.
intros n m.
intros H.
(* Используем тактику rewrite *)
rewrite -> H.
reflexivity.
Qed.

(* Тактика rewrite заключается в следующем
intros H переносит гипотезу в контекст доказательства
rewrite -> H. говорит о том, что нужно переписать в соответствии с гипотезой левую часть уравнения
rewrite <- H. говорит о том, что нужно переписать правую часть (разницу видно при пошаговом исполнении)
 *)

Theorem plus_id_example2: forall n m: nat, n = m -> n + n = m + m.
Proof.
intros n m.
intros H.
(* Используем тактику rewrite *)
rewrite <- H.
reflexivity.
Qed.

(* Здесь в теореме определяется сразу два условия: n = m и m = k *)
Theorem plus_id_example3: forall n m k: nat, n = m -> m = k -> n + m = m + k.
Proof.
intros n m k.
(* Загружаем обе гипотезы *)
intros H1 H2.
(* Используем тактику rewrite дважды *)
(* Первой гипотезой переписываем левую часть, а второй - правую *)
rewrite -> H1.
rewrite <- H2.
reflexivity.
Qed.



(*
Эту функцию можнобыло бы определить как в 2.v, но тут, для эксперимента берём вложенные match
Функция неверная, см. комментарии в функции
 *)
Fixpoint plusVin(n m : nat) : nat :=
  match n with
	| O => 
		match m with
			| O    => n
			| _    => m
		end
	| S n' =>
		match m with
			(* Если сюда поставить S (plusVin n' O) или другой вызов plusVin - не поймёт
				The reference plusVin was not found in the current environment.
				Впечатление, что он считает, 
				что в любом match должна быть одна ветка без рекурсии *)
			| O    => n
			| S m' => S (plusVin n' m')
		end
  end.

Fixpoint plusVinA(n m : nat) : nat :=
  match n with
	| O => 
		match m with
			| O    => O
			| S m' => S (plusVinA O m')
		end
	| S n' =>
		match m with
			(* Если сюда поставить S (plusVin n' O) или другой вызов plusVin - не поймёт
				Cannot guess decreasing argument of fix.
				Функция plusVin абсолютно аналогична, но из-за теоремы ниже ошибки разные
				То есть с выводом ошибок всё не так просто:
				может быть выведена следующая за определением ошибка *)
			| O    => S (n')
			| S m' => S (plusVinA n' m')
		end
  end.

Theorem plusVin_O_O : forall n : nat, (plusVin O O) = O.
Proof.
  intros n.
  simpl. reflexivity. Qed.
  
Theorem plusVin_O_1 : forall n : nat, (plusVin O (S(O))) = S(O).
Proof.
  intros n.
  simpl. reflexivity. Qed.
(* Тоже не может, хотя 0 + n = n доказывает
Theorem plusVin_O_n : forall n : nat, (plusVin O n) = n.
Proof.
  intros n.
  simpl. reflexivity. Qed.
*)
(* К сожалению, эту теорему он доказать не может
Theorem plus_m_n : forall n m : nat, (plusVin m n) = (plusVin n m).
Proof.
  intros n m.
  simpl. reflexivity. Qed.
*)

(* На этой функции выдаёт ошибку:
 Cannot guess decreasing argument of fix.
 Похоже, рекурсивный аргумент должен быть только один
 *)
(*
Fixpoint plusVin2(n m : nat) : nat :=
  match n, m with
	| O,    O    =>  O
	| O,    S m' => S (plusVin2 O m')
	| S n', O    => S (plusVin2 n' O)
	| S n', S m' => S (plusVin2 n' m')
  end.
*)

Fixpoint plusVin3(n m : nat) : nat :=
  match n, m with
	| O,    O    => O
	| O,    S m' => m
	| S n', O    => n
	| S n', S m' => S (S (plusVin3 n' m'))
  end.

(* С этой функцией тоже не получается доказать, что 0+n = n *)
Theorem plus_0_0_Vin3 : forall n : nat, (plusVin3 0 0) = 0.
Proof.
  intros n.
  simpl. reflexivity. Qed.

(* Это никак не доказывается *)
(*
Theorem plus_0_n_Vin3 : forall n : nat, n > 0 -> (plusVin3 0 n) = n.
Proof.
  intros n.
  intros H.
  simpl.
  rewrite -> H.
  simpl. reflexivity.
Qed.
*)


(* К сожалению, эту теорему он тоже доказать не может *)
(*
Theorem plus_m_n : forall n m : nat, (plusVin3 m n) = (plusVin3 n m).
Proof.
  intros n m.
  simpl. reflexivity. Qed.
*)

Fixpoint plusVin4(n m : nat) : nat :=
  match n with
	| O    => m
	| S n' => S(plusVin4 n' m)
  end.

(* А вот это он доказывает на ура *)
Theorem plus_0_n_Vin4 : forall n : nat, (plusVin4 0 n) = n.
Proof.
  intros n.
  simpl. reflexivity. Qed.

