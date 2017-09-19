(** * 리스트: 구조적 데이터를 가지고 작업하기 *)

Require Export Induction.
Module NatList.

(* ################################################################# *)
(** * 숫자들의 쌍들 *)

(** [Inductive] 정의에서 각 생성자는 어떤 개수의 인자들을 받을 수
    있다. [true]와 [O]와 같이 인자를 받지 않는 생성자, [S]와 같이
    하나의 인자를 받는 생성자가 있고, 다음 예에서 하나 이상을 받는
    생성자를 보여준다. *)

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

(** 이 선언을 읽는 법은 "숫자들 쌍을 만드는 단 한 가지 방법이 있는데,
    생성자 [pair]를 [nat] 타입의 두 인자들에 적용하는 것이다."  *)

Check (pair 3 5).

(** 쌍에서 첫 번째와 두 번째 요소들을 꺼내는 두 개의 간단한 함수들이
    있다.  이 정의들은 또한 두 개의 인자를 받은 생성자들에 대해 패턴
    매치를 하는 법도 보여준다. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(** 쌍들은 상당히 자주 사용되기 때문에 [pair x y] 대신에 표준 수학
    표기법 [(x,y)]으로 쓸 수 있으면 좋을 것이다. 콕에서 [Notation]
    선언으로 가능하다. *)

Notation "( x , y )" := (pair x y).

(** 쌍에 대한 새로운 표기법은 식과 패턴 매치에서 모두 사용될 수
    있다. ([Basics] 장의 [minus] 함수의 정의에서 사실 이미
    보았다. 표준 라이브러리 일부로 쌍에 대한 표기법도 제공하기 때문에
    동작한 것이다. *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** 쌍들에 대한 몇 가지 간단한 사실들을 증명해보자.

    특별한 방법으로 이 명제들을 서술하면 reflexivity (와 그리고 내장된
    간략화) 만으로 증명들을 완성할 수 있다. *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(** 하지만 만일 보조 정리를 더 자연스러운 방법으로 서술하면
    [reflexivity]만으로 충분하지 않다. *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* 아무것도 간략화되지 않는다! *)
Abort.

(** [p]의 구조를 드러내서 [simpl]로 [fst]와 [snd]에서의 패턴 매치를
    수행할 수 있어야 한다. 이것은 [destruct]를 가지고 할 수 있다. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(** [nat] 타입의 값들을 가지고 다룰 때와 달리 [destruct]는 단 하나의 부분
    목적 만을 만든다는 것을 주목하시오. [natprod] 타입의 값들은 한 가지 방법으로만
    생성할 수 있기 때문이다. *)

(** **** 연습문제: 별 하나 (snd_fst_is_swap)  *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 하나, 선택사항 (fst_swap_is_snd)  *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 숫자 리스트 *)

(** 쌍에 대한 정의를 일반화하면 다음과 같이 숫자 _리스트_의 타입을
    기술할 수 있다.  "리스트는 비어있는 리스트이거나 숫자와 또 다른
    리스트의 쌍이다." *)

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

(** 예를 들어, 세 개의 원소를 갖는 리스트가 여기 있다. *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** 쌍들을 다룰 때와 같이 익숙한 프로그래밍 표기법으로 리스트를 쓰는 것이 
    더 편리하다. 다음 선언들로 [::]을 중위 표기 [cons]로 사용하고 
    대괄호를 리스트를 만드는 "바깥쪽을 감싸는" 표기법으로 사용할 수 있다. *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** 이 선언들을 자세하게 이해할 필요는 없지만 관심이 있다면 여기 대강
    설명한다.  [right associativity] 주석을 달아 콕으로 하여금 [::]을
    여러 번 사용한 식 들에서 괄호를 어떻게 씌울지 정한다. 예를 들어
    다음 세 가지 선언들은 모두 동일한 의미를 갖는다. *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** [at level 60]은 [::]과 다른 중위 연산자를 함께 사용한 식들에서
    괄호를 어떻게 매길지 정한다. 예를 들어, [+]를 [plus] 함수에 대한
    중위 표기법으로 50 레벨로 정의하였기 때문에,

  Notation "x + y" := (plus x y) (at level 50, left associativity).

   [+] 연산자는 [::]보다 더 빨리 묶인다. 그래서 [1 + 2 :: [3]]은 콕이
   우리가 기대한 대로 [(1 + 2) :: [3]]으로 해석하고, [1 + (2 ::
   [3])]으로 해석하지 않는다.

   (.v 파일에서 "[1 + 2 :: [3]]"와 같은 식을 읽을 때 조금 혼동스러울
   수 있다. 3을 감싸는 안쪽 괄호는 리스트를 표시하지만, 바깥쪽
   괄호(HTML에서 보이지 않는)는 "coqdoc" 도구가 텍스트가 아니라 콕
   코드로 표시해야 한다는 명령어이다.)

   위에서 두 번째와 세 번째 [Notation] 선언들은 리스트에 대한 표준
   대괄호 표기법을 도입한다. 세 번째 선언의 오른편은 콕에서 n개를
   나열하는 표기법을 사용하는 예시를 보여주고 이진 생성자들의 반복해서
   내포된 형태로 변환되는 예를 설명한다. *)

(* ----------------------------------------------------------------- *)
(** *** Repeat *)

(** 많은 함수들이 리스트를 다루기에 유용하다. 예를 들어, [repeat]
    함수는 [n]과 [count]를 받아 모든 원소가 [n]이고 길이가 [count]인
    리스트를 반환한다. *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* ----------------------------------------------------------------- *)
(** *** Length *)

(** [length] 함수는 리스트의 길이를 계산한다. *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Append *)

(** [app] 함수는 두 리스트들을 붙여 하나의 리스트를 만든다. *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** 사실 [app]은 뒤이어 나올 어떤 부분에서 많이 사용될 것이다. 그래서
    중위 표기법을 도입하는 것이 편리하다.  *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** (기본 값을 지정한) Head와 Tail *)

(** 리스트 프로그래밍의 두 가지 작은 예제가 있다. [hd] 함수는 인자로
    주어진 리스트의 첫 번째 원소 ("head")를 반환하고 [tl] 함수는 첫
    번째 원소를 제외한 모든 것 ("tail")을 리턴한다. 물론 비어 있는
    리스트는 첫 번째 원소가 없기 때문에 그런 경우에 리턴할 기본 값을
    지정해야 한다. *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.


(* ----------------------------------------------------------------- *)
(** *** 연습문제들 *)

(** **** 연습문제: 별 두 개, 추천 (list_funs)  *)
(** 아래의 [nonzero], [oddmembers], [countoddmembers] 정의를
    완성하시오.  이 함수들이 하는 일을 이해하기 위해 테스트들을 살펴
    보시오. *)

Fixpoint nonzeros (l:natlist) : natlist
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  (* 여기를 채우시오 *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  (* 여기를 채우시오 *) Admitted.

Definition countoddmembers (l:natlist) : nat
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  (* 여기를 채우시오 *) Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  (* 여기를 채우시오 *) Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개, 고급 (alternate)  *)
(** 두 리스트를 "지퍼로 잠그는 방식"으로 첫 번째 리스트에서 취한
    원소들과 두 번째 리스트에서 취한 원소들 사이를 번갈아 가며 하나의
    리스트로 만들도록 [alternate]를 완성하시오.

    [alternate]를 자연스럽고 우아하게 작성하려면 콕에서 요구하는 모든
    [Fixpoint] 정의들이 "분명하게 종료해야 한다"는 점을 만족시키지
    못할 것이다. 그 대신 두 리스트들의 원소들을 동시에 고려하는 조금
    더 긴 해법을 찾아보시오. (한 가지 가능한 해는 새로운 종류의 쌍들을
    정의하는 것인데 이 것이 유일한 방법은 아니다.  *)

Fixpoint alternate (l1 l2 : natlist) : natlist
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  (* 여기를 채우시오 *) Admitted.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  (* 여기를 채우시오 *) Admitted.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  (* 여기를 채우시오 *) Admitted.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** 리스트로 표현한 가방(bags) 자료 구조 *)

(** [bag] (또는 [multiset])은 집합과 같다. 다만, 각 원소가 단 한 번이
    아니라 여러 번 나타날 수 있다는 점이 다르다. 숫자들을 담은 가방
    자료 구조를 표현하는 한 가지 가능한 구현은 리스트를 사용하는
    것이다.  *)

Definition bag := natlist.

(** **** 연습문제: 별 세 개, 추천 (bag_functions)  *)
(** 가방 자료 구조를 다루는 [count], [sum], [add], [member] 함수들의
    정의를 완성하시오. *)

Fixpoint count (v:nat) (s:bag) : nat
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

(** 아래 증명들은 모두 [reflexivity]만 사용해도 증명할 수 있다. *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* 여기를 채우시오 *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* 여기를 채우시오 *) Admitted.

(** 중복 집합 [sum]은 집합 [union]과 유사하다. [sum a b]는 [a]와 [b]의
    모든 원소들을 포함한다. (수학자들은 대개 중복 집합에 대한
    [union]을 sum 대신 max를 사용하여 조금 다르게 정의한다. 이 연산에
    대해 [union]이라고 부르지 않는 이유이다. [sum]의 정의에서 인자
    이름을 명시적으로 주지 않고 작성하고 있다. 더욱이 [Fixpoint] 대신
    [Definion] 키워드를 사용한다.  따라서 그 인자들 이름을 지었더라도
    재귀 방식으로 다룰 수 없을 것이다. 이런 식으로 문제를 제시하는
    의도는 스스로 [sum]이 다른 방식으로 구현될 수 있는지 생각해보라는
    것이다. 아마도 이미 정의했던 함수들을 사용할 수 있다.  *)

Definition sum : bag -> bag -> bag
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* 여기를 채우시오 *) Admitted.

Definition add (v:nat) (s:bag) : bag
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* 여기를 채우시오 *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* 여기를 채우시오 *) Admitted.

Definition member (v:nat) (s:bag) : bool
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_member1:             member 1 [1;4;1] = true.
 (* 여기를 채우시오 *) Admitted.

Example test_member2:             member 2 [1;4;1] = false.
 (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개, 선택사항 (bag_more_functions)  *)
(** 여기 가방 자료 구조를 다루는 함수들이 있으니 연습해보시오.  *)

(** remove_one을 제거할 숫자를 포함하지 않는 가방 자료 구조에 적용하면 
    동일한 가방을 변경하지 않고 반환해야 한다. *)

Fixpoint remove_one (v:nat) (s:bag) : bag
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  (* 여기를 채우시오 *) Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  (* 여기를 채우시오 *) Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  (* 여기를 채우시오 *) Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* 여기를 채우시오 *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* 여기를 채우시오 *) Admitted.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* 여기를 채우시오 *) Admitted.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* 여기를 채우시오 *) Admitted.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* 여기를 채우시오 *) Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 (* 여기를 채우시오 *) Admitted.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개, 추천 (bag_theorem)  *)
(** 함수 [count]와 [add]와 관련된 가방 자료 구조에 대한 흥미로운 정리
    [bag_theorem]를 작성하고 증명하시오. 이 것은 열린 문제이기 때문에
    참인 정리이지만 증명하기 위해서 아직 배우지 않은 방법이 필요할
    수도 있다.  막히면 자유롭게 질문하시오! *)

(*
Theorem bag_theorem : ...
Proof.
  ...
Qed.
*)

(** [] *)

(* ################################################################# *)
(** * 리스트에 대한 추론 *)

(** 숫자들을 다루었을 때처럼 리스트 처리 함수들에 대한 간단한 사실들은
    종종 간략화를 통해 완전히 증명할 수 있다. 예를 들어,
    [reflexivity]로 간략화를 수행하면 아래 정리를 충분히 증명할 수
    있다...  *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ... 왜냐하면 [[]]을 [app] 정의에서 match로 조사할 식으로 대체해서
    그 매치 자체가 간략화되기 때문이다. *)

(** 그리고 숫자들에 대해서와 같이 알려지지 않은 리스트의 가능한 형태에
    관해 경우 별로 분석하는 것이 도움이 될 수 있다. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

(** 여기 [nil]의 경우 [tl nil = nil]로 정의하였기 때문에 증명할 수
    있다.  [destruct] 전술에 [as] 주석으로 [n]과 [l'] 이름들을 여기
    도입한다.  리스트에 대한 [cons] 생성자의 두 인자들(리스트의 머리와
    꼬리)에 이 이름들을 붙인다. *)

(** 비록 리스트에 대한 흥미로운 정리들을 증명하려면 대개 귀납법이
    필요하다. *)

(* ----------------------------------------------------------------- *)
(** *** 짧은 설교 *)

(** 예제 증명 스크립트들을 읽기만 하면 제대로 이해하지 못할 것이다!
    콕을 사용하고 각 단계가 얻는 바를 생각하면서 각 증명의 상세 내용을
    따라가는 것이 중요하다.  그렇지 않으면 증명들을 시작할 때
    연습문제들은 아무런 의미가 없을 것이 분명하다.  충분히
    얘기했다. *)

(* ================================================================= *)
(** ** 리스트에 대한 귀납법 *)

(** [natlist] 같은 자료형들에 대한 귀납법으로 증명하는 것은 자연수에
    대한 귀납법 보다 조금 덜 익숙 할 수 있지만 아이디어는 똑같이
    간단하다. 각 [Inductive] 선언은 선언한 생성자들을 사용하여 만들 수
    있는 데이터 값들의 집합을 정의한다. 부울형은 [true] 또는
    [false]이고 숫자는 [O]와 [S]를 다른 숫자에 적용한 것이고, 리스트는
    [nil] 또는 숫자와 리스트에 적용한 [cons]이다.

    더욱이 선언한 생성자들을 다른 것에 적용하는 것만이 유일하게
    귀납적으로 정의한 집합의 원소들이 가질 수 있는 _유일하게_ 가능한
    모양이다. 그리고 이러한 사실을 통해 귀납적으로 정의된 집합들에
    대해 유추하는 방법을 직접적으로 제공한다. 숫자는 [O]이거나 그렇지
    않으면 [S]를 _더 작은_ 숫자에 적용한 것이고, 리스트는 [nil]이거나
    그렇지 않으면 [cons]를 어떤 숫자와 어떤 _더 작은_ 리스트에 적용한
    것이며, 등등. 그래서 리스트 [l]을 언급하는 어떤 명제 [P]가 있고,
    _모든_ 리스트에 대해 [P]가 성립한다고 주장하고 싶다면 다음과 같이
    추론할 수 있다.

      - 첫째, [l]이 [nil] 일 때 [P]가 참이라고 증명하시오.

      - 그런 다음 [l]이 어떤 숫자 [n]과 어떤 작은 리스트 [l']에 대한
        [cons n l'] 일 때, [P]가 [l']에 대해 참이라고 가정하에 [P]가
        참임을 보이시오.

    더 큰 리스트는 오직 더 작은 리스트들 (궁극적으로 [nil]에 도달할 것인)로
    만들기 때문에 이 두 주장들을 합하면 [P]가 모든 리스트 [l]에 대해 참이라는
    것을 증명한다. 여기 구체적인 예가 있다. *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** 자연수에 대한 귀납법을 적용할 때처럼 [induction] 전술에서 [cons]
    경우에 [as...] 절로 더 작은 리스트 [l1']에 해당하는 귀납 가정에
    이름을 붙인다. 다시 한번 반복하면, 이 콕 증명은 고정된 형태로
    작성한 문서로 보아서는 더욱 안된다. 대화식 콕 세션에서 증명을 읽고
    있다면 무엇이 진행되고 있는지 쉽게 알 수 있고 현재 목적과 문맥을
    각 지점에서 볼 수 있다. 하지만 이러한 상태는 콕 증명으로 작성한
    부분에서는 드러나 있지 않다. 그래서 사람을 위해서 작성한 자연어로
    서술된 증명은 더 명백한 이정표를 포함할 필요가 있을 것이다. 특히
    두 번째 경우에 귀납적 가정이 무엇인지 독자들에게 정확히
    환기시킨다면 증명의 흐름을 잃지 않도록 유지하는데 도움이 될
    것이다. *)

(** 비교를 위해 여기 동일한 정리를 비형식적으로 증명해본다. *)

(** _정리_: 모든 리스트 [l1], [l2], [l3]에 대하여,
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _증명_: [l1]에 관한 귀납법에 의하여.

   - 첫째, [l1 = []]라 가정하자.  다음을 증명해야 한다.

       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

     [++] 정의에 의해 바로 성립한다.

   - 다음은, 아래 등식이 성립하는 [l1 = n::l1']을 가정하자.

       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

     (귀납 가정). 다음 등식이 성립함을 보여야 한다.

       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

     [++] 정의와 아래 등식에 의해 성립한다.

       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

     위 등식은 귀납 가정에 의해 바로 성립한다.  [] *)

(* ----------------------------------------------------------------- *)
(** *** 리스트 뒤집기 *)

(** 리스트에 대한 조금 더 어려운 귀납 증명의 예에 대해 리스트 뒤집는
    함수 [rev]를 [app]를 사용해서 정의한다고 가정하자. *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** [rev]의 성질들 *)

(** 새롭게 정의한 [rev]에 대한 몇 가지 정리들을 이제
    증명해보자. 지금까지 본 것보다 조금 더 도전적인 증명으로 리스트를
    뒤집으면 그 길이가 달라지지 않는다는 것을 증명하자.  처음
    귀납법으로 증명해보면 비어있지 않는 리스트의 경우에서 막힌다... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    (* 이 것은 까다로운 경우이다. 그동안 증명해온 것과 같이 간략화로 시작해보자. *)
    simpl.
    (* 이제 막힌 것처럼 보인다. 이 목적은 [++]를 포함한 등식이지만
       현재 문맥이나 전역 환경에서 증명에 유용한 등식이 없다! IH를 사용해서
       현재 목적을 다시 작성하면 약간 증명을 진행할 수 있다...  *)
    rewrite <- IHl'.
    (* ... 하지만 이제 더이상 나아갈 수 없다. *)
Abort.

(** [++]와 [length]를 연관 짓는 등식을 취하자. 이 등식으로 증명을
    진행할 수도 있고 별도의 보조 정리로 증명할 수도 있을 것이다. *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** 이 보조 정리를 가능한 일반화시키기 위해, [rev] 적용 결과에 대한
    것이 아닌 _모든_ [natlist]들에 대해 한정사를 두었다. 이 목적이
    참인지 여부는 분명히 뒤집을 리스트에 의존하지 않기 때문에 이렇게
    한정사를 두는 것이 자연스럽다. 더욱이 더 일반적인 성질을 증명하기
    더 쉽다. *)

(** 이제 원래 증명을 완성할 수 있다. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'. reflexivity.  Qed.

(** 비교를 위해 두 정리들을 비형식적으로 증명한 것이 여기 있다.

    _정리_: 모든 리스트 [l1]과 [l2]에 대해 
       [length (l1 ++ l2) = length l1 + length l2].

    _증명_: [l1]에 대한 귀납법에 의해.

    - 첫째, [l1 = []]을 가정하자.  다음을 증명하자.

        length ([] ++ l2) = length [] + length l2,

      [length]와 [++]의 정의들로 부터 바로 보일 수 있다.

    - 다음으로, 아래 등식과 함께 [l1 = n::l1']을 가정하자.

        length (l1' ++ l2) = length l1' + length l2.

      다음을 증명해야 한다.

        length ((n::l1') ++ l2) = length (n::l1') + length l2).

      [length]와 [++] 정의들과 귀납 가정과 함께 바로 보일 수 있다. [] *)

(** _정리_: 모든 리스트 [l]에 대해, [length (rev l) = length l].

    _증명_: [l]에 관한 귀납법에 의해.

      - 첫째, [l = []]를 가정하자.  다음 등식을 증명해야 한다.

          length (rev []) = length [],

        이 등식은 [length]와 [rev] 정의들에서 직접 유도할 수 있다.

      - 다음으로, 아래 등식과 함께 [l = n::l']를 가정하자

          length (rev l') = length l'.

        다음 등식을 증명해야 한다.

          length (rev (n :: l')) = length (n :: l').

        [rev] 정의에 의해, 위 등식은 아래 등식으로 증명할 수 있는데,

          length ((rev l') ++ [n]) = S (length l')

        이전 보조 정리에 의해 이 등식은 아래 등식과 동일하다.

          length (rev l') + length [n] = S (length l').

        동일한 이 등식은 귀납 가정과 [length] 정의에 의해 바로 보일 수 있다. *)

(** 이 증명들 스타일은 꽤 지루하고 현학적이다. 이 증명들 처음 두
    세 개를 살펴보면, 상세한 내용이 적은 (머리 속으로 또는 필요하다면
    메모 용지에 쉽게 작성할 수 있는) 그리고 중요한 단계들만 강조하는
    증명들을 따라가기가 더 쉽다는 것을 발견할 수 있다. 이런 더 압축된
    스타일로 위 증명을 다시 작성하면 다음과 같이 보일 것이다.  *)

(** _정리_: 모든 리스트 [l], [length (rev l) = length l]에 대해.

    _증명_: 첫째, 어떤 [l]에 대해 [length (l ++ [n]) = S (length
     l)]이다.  ([l]에 대한 직접적인 귀납 증명으로 보일 수 있다.)

     그 주요 성질은, [l = n'::l'] 경우의 귀납 가정과 함께 위 등식을
     사용하여 [l]에 대한 귀납법으로 다시 보일 수 있다. *)

(** 주어진 상황에서 어느 스타일이 더 좋은지는 기대하는 독자의 교육
    정도와 독자가 이미 익숙한 증명과 얼마나 비슷한지에 따라 다르다. 더
    현학적인 스타일이 현재 목적을 위한 좋은 초기 설정이다. *)

(* ================================================================= *)
(** ** [Search] *)

(** 예를 들어 [rewrite]를 사용하여, 이미 증명한 다른 정리들을 이용하여
    증명하는 것을 보았다.  그러나 어떤 정리를 참조하기 위해 이름을 알
    필요가 있다! 정말로 이전에 증명한 정리들을 기억하는 것 조차 종종
    어렵고 또한 그 정리들의 이름들은 더 기억하기 어렵다.

    콕의 [Search] 명령은 이럴 때 꽤 도움이 된다. [Search foo]를 치면 콕은 [foo]가
    포함된 모든 정리들의 목록을 보여줄 것이다. 예를 들어, [rev]에 대해 증명했던 정리들의
    목록을 보기 위해서 다음 주석을 제거해보라. *)

  Search rev. 

(** 다음 연습문제들을 풀 때 그리고 이 책을 읽는 동안 [Search]를
    기억하라. 왜냐하면 많은 시간을 절약하게 해줄 것이기 때문이다!

    프룹제너럴(ProofGeneral)을 사용하면 [C-C C-a C-a]를 가지고
    [Search]를 실행할 수 있다. [C-c C-;] 명령어로 그 결과를 버퍼로
    옮겨올 수 있다. *)

(* ================================================================= *)
(** ** 리스트 연습문제들, 파트 1 *)

(** **** 연습문제: 별 세 개 (list_exercises)  *)
(** 리스트에 대한 추가 연습: *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* 여기를 채우시오 *) Admitted.

(** 다음 연습문제에 대한 짧은 해가 있다. 증명이 엉키면 뒤로 물러나서
    더 간단한 방법을 찾아보려고 노력해보라. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* 여기를 채우시오 *) Admitted.

(** [nonzeros]의 구현에 대한 연습문제: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 두 개 (beq_natlist)  *)
(** [beq_natlist] 정의를 채우시오. 이 함수는 두 리스트의 숫자들이 같은
    지 비교한다. 모든 리스트 [l]에 대해 [beq_natlist l l]는 [true]를
    냄을 증명하시오.  *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
 (* 여기를 채우시오 *) Admitted.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
(* 여기를 채우시오 *) Admitted.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
 (* 여기를 채우시오 *) Admitted.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 리스트 연습문제들, 파트 2 *)

(** **** 연습문제: 별 세 개, 고급 (bag_proofs)  *)
(** 위의 가방 자료구조에 대해 정의들에 관하여 증명하는 한 두 가지 작은
    정리들이 있다. *)

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  (* 여기를 채우시오 *) Admitted.

(** [leb]에 대한 다음 보조 정리는 다음 증명에 도움이 될 수도 있다. *)

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개, 선택사항 (bag_count_sum)  *)
(** 함수 [count]와 [sum]을 사용하는 가방 자료 구조에 대한 정리
    [bag_count_sum]을 흥미롭게 작성하고 증명해보시오. ([count]를
    정의하는 법에 따라 그 증명이 어려울 수도 있다!)  *)
(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 네 개, 고급 (rev_injective)  *)
(** [rev] 함수가 단사 함수임을 증명하시오. 즉,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

(어렵게 증명하는 방법과 쉽게 증명하는 방법이 있다.) *)

(* 여기를 채우시오 *)
(** [] *)

(* ################################################################# *)
(** * 선택사항들 *)

(** 어떤 리스트의 [n]번째 원소를 반환하는 함수를 작성한다고
    가정하자. 그 함수의 타입을 [nat -> natlist -> nat]로 하면 리스트가
    너무 짧을 때 리턴할 어떤 숫자를 선택해야 할 것이다...  *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

(** 위 정의는 그다지 좋지 않다. 왜냐하면 [nth_bad]가 [42]를 반환하면
    입력 리스트에 값이 실제로 나타나는지 추가 처리 없이 구분할 수 없기
    때문이다.  더 나은 대응 방법은 [nth_bad]의 반환 타입을 변경해서
    가능한 결과 중 하나로 에러 값을 포함시키는 것이다. 이러한 타입을
    [natoption]이라고 부른다. *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(** 위 [nth_bad] 정의를 변경해서 리스트가 너무 짧을 때 [None]를
    반환하고 리스트가 충분한 원소들로 구성되어 [n] 위치에 [a]가 나타날
    때 [Some a]를 리턴할 수 있다. 이 새로운 함수를 [nth_error]으로
    이름 지어 에러를 결과로 낼 수 있음을 나타낸다.  *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(** (In the HTML version, the boilerplate proofs of these
    examples are elided.  Click on a box if you want to see one.)

    This example is also an opportunity to introduce one more small
    feature of Coq's programming language: conditional
    expressions... *)


Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

(** 콕의 조건식은 다른 언어의 조건식과 한 가지 작은 일반화를 제외하고
    정확히 똑같다.  부울이 기본으로 제공되는 타입이 아니기 때문에
    실제로 콕은 정확히 두 가지 생성자들을 가지고 _어떤_ 귀납적으로
    정의한 타입에 대한 조건식을 지원한다. 조건식을 계산해서
    [Inductive] 정의의 첫 번째 생성자가 나오면 참이고, 두 번째
    생성자가 나오면 거짓이라고 간주한다. *)

(** 아래 함수는 [natopion]에서 [nat]을 꺼내고 [None] 경우에 제공된
    기본 값을 반환한다. *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** 연습문제: 별 두 개 (hd_error)  *)
(** 동일한 아이디어를 사용하여 초기 [hd] 함수를 [nil] 경우에 기본
    원소를 전달하지 않아도 되도록 수정하시오.  *)

Definition hd_error (l : natlist) : natoption
  (* 이 줄을 ":= 로 시작하는 정의"로 바꾸시오. *). Admitted.

Example test_hd_error1 : hd_error [] = None.
 (* 여기를 채우시오 *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
 (* 여기를 채우시오 *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 하나, 선택사항 (option_elim_hd)  *)
(** 이 연습문제는 새로운 함수 [hd_error]를 예전 함수 [hd]와 연관짓는다. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

End NatList.

(* ################################################################# *)
(** * 부분 맵 *)

(** 콕에서 어떤 자료 구조를 정의할 수 있는지 설명하는 마지막 예로
    간단한 _부분 맵_ 자료 타입이 있다. 대부분의 프로그래밍언어에 있는
    맵이나 딕셔너리 자료 구조와 유사하다. *)

(** 첫째, 새로운 귀납적 자료형 [id]를 정의해서 부분 맵의 "키"로 사용한다. *)

Inductive id : Type :=
  | Id : nat -> id.

(** 내부적으로 [id]는 단지 숫자이다. 각 숫자를 [Id] 태그로 감싸 별도의
    타입을 도입하면 정의들이 더 읽기 좋고 나중에 우리가 원하면 표현을
    변경시킬 수 있는 유연성을 제공한다.

    [id]들이 똑같은지 테스트할 필요가 있을 것이다. *)

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(** **** Exercise: 1 star (beq_id_refl)  *)
Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** 이제 부분 맵의 타입을 정의한다: *)

Module PartialMap.
Export NatList.
  
Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.

(** 이 선언을 다음과 같이 읽을 수 있다. "[partial_map]을 만드는 두
    가지 방법이 있다. [empty] 생성자를 사용하여 비어 있는 부분 맵을
    표현하거나 [record] 생성자를 키와 값과 다른 [partial_map]에
    적용하여 기존 부분 맵에 키와 값 매핑을 추가하여 [partial_map]을
    만든다." *)

(** [update] 함수는 부분 맵에서 주어진 키에 대한 내용을 바꾸거나
    주어진 키가 아직 없으면 새로운 내용을 추가한다.  *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(** 마지막으로 [find] 함수는 [partial_map]에서 주어진 키를 탐색한다.
    그 키를 찾지 못하면 [None]를 반환하고, 그 키와 [val]이 연관되어
    있다면 [Some val]을 리턴한다. 만일 같은 키가 여러 값들에 매핑되어
    있으면 [find]는 첫 번째로 만나는 것을 반환할 것이다. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.


(** **** 연습문제: 별 하나 (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
 (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 하나 (update_neq)  *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
 (* 여기를 채우시오 *) Admitted.
(** [] *)
End PartialMap.

(** **** 연습문제: 별 두 개 (baz_num_elts)  *)
(** 아래의 귀납적 정의를 고려하자: *)

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

(** [baz] 타입은 _몇 개_의 원소들을 가지고 있는가? (영어로 답하거나
    당신의 언어로 답하시오.)

(* 여기를 채우시오 *)
*)
(** [] *)

(** $Date: 2017-08-24 10:54:05 -0400 (Thu, 24 Aug 2017) $ *)



(* Local Variables: *)
(* coq-prog-name: "/Applications/CoqIDE_8.6.1.app/Contents/Resources/bin/coqtop" *)
(* coq-load-path: nil *)
(* End: *)
