
(* Это многострочный комментарий
В нём нужно соблюдать парность кавычек строковых литералов
Многострочные комментарии могут быть вложены
*)

(*
Тип-перечисление day
Состоит из перечисления вариантов.
Заканчивается точкой (точку можно поставить на отдельной строке, чтобы обратить на неё внимание).
*)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* Определяем функцию для работы с днями
В Coq есть вывод типов, поэтому типы явно указывать не надо

Сопоставление с образцом выведет ошибку, если предусмотрены не все варианты
*)
Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday
  | sunday    => monday
  end
  .

(*
Определяем некорректную функцию next_weekday
*)
Definition next_weekday_incorrect (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end
  .

(*
Значение функции можно вычислить с помощью Compute
Оно будет выведено на консоль CoqIDE
Вызов идёт без скобок: сначала имя функции, потом параметры, например:
next_weekday friday

Однако, если нужно получить значение этой функции, то её берут в скобки,
так что это становится на синтаксис Lisp
 *)
Compute (next_weekday friday).

(*
Example - это пример
Он имеет имя
По сути, он является утверждением, которое можно по этому имени, например, доказать
То есть на него затем можно ссылаться по имени
*)
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = monday
  .

(* Доказываем *)
Proof. simpl. reflexivity. Qed.

(*
Следующее утверждение даст ошибку при доказаетльстве
Unable to unify "monday" with "wednesday".
     = saturday
     : day
*)

(*
Example test_next_weekday_incorrect:
  (next_weekday_incorrect (next_weekday_incorrect saturday)) = monday.

(* Доказываем то, что неверно и получаем ошибку *)
Proof. simpl. reflexivity. Qed.
*)


(*
Если написать только один раз в конце программы
Proof. simpl. reflexivity. Qed.
то выдастся ошибка

Nested proofs are not allowed unless you turn the Nested Proofs Allowed flag on.

То есть нужно сначала доказать теоремы выше, а потом уже ниже (или установить возможность вложенных доказательств).
*)


Example test_next_weekday7:
  (next_weekday (next_weekday (next_weekday (next_weekday (next_weekday (next_weekday (next_weekday monday))))))) = monday
  .

Proof. simpl. reflexivity. Qed.

(*
Example test_next_weekday_notequal:
	(next_weekday monday) <> monday
	.

Proof. simpl. reflexivity. Qed.

Example test_next_weekday_incorrect_notequal:
	(next_weekday_incorrect monday) <> monday
	.

Proof. simpl. reflexivity. Qed.
*)

(*
При этом определяем также свой модуль VinBool: в конце определения не забываем точку!
Модуль VinBool заканчивается сторокой End VinBool.
Обращаем внимание на то, что End пишется с большой буквы и точку после имени модуля.

Всё, что внутри модуля, будет доступно теперь через точку: VinBool.bool и т.п.
*)
Module VinBool.

(*
Определяем булевский тип операций (он уже определён в стандартной библиотеке)
*)
Inductive bool : Type :=
  | true
  | false
  .

Definition negb (b:bool) : bool :=
  match b with
  | true  => false
  | false => true
  end
  .

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true  => b2
  | false => false
  end
  .

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true  => true
  | false => b2
  end
  .

(*
Определяем нотацию булевского типа
*)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).


(*
Ключевое слово "Admitted" оставляет доказательство/определение в исходниках незавершённым (допущение)
В полосе CoqIDE ошибки подсвечиваются красным, а Admitted подсвечивается оранжевым и в ошибках не значится
*)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Example test_andb31: (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.

End VinBool.
