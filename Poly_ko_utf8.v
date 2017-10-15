(** * Poly: 다형성과 고차원 함수 *)

(* 마지막 알림: 연습문제들에 대한 해답을 공개적으로 접근 가능한 곳에
   두지 마시오. 감사합니다!!  *)

(* Coq에서 일부 귀찮은 경고들을 내지 않도록 하려면: *)
Set Warnings "-notation-overridden,-parsing".
Require Export Lists.

(*** 다형성 *)

(** 이 장에서 함수형 프로그래밍의 기본 개념들을 계속 발전시킨다.
    중요한 새로운 생각은 _다형성_ (함수가 다루는 데이터의 타입에 관해
    함수를 추상화)과 _고차원 함수_ (함수를 데이터로 다루기)이다.
    다형성부터 시작한다.  *)

(* ================================================================= *)
(** ** 다형 리스트 *)

(** 지난 두 장에서 단지 숫자 리스트를 가지고 논의해왔었다. 흥미로운 프로그램이라면 분명히
    다른 타입의 원소들로 구성된 리스트들을 다룰 있어야 한다. 문자열 리스트, 부울 리스트,
    리스트의 리스트 등. 각 종류의 리스트에 대해 새로운 귀납적 데이터 타입을 _정의할 수도_
    있다. 예를 들어... *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(** ... 하지만 이렇게 매번 새로 정의하는 것은 금방 지루한 일이 될
    것이다. 왜냐하면 각 데이터 타입에 대해 다른 생성자 이름들을
    만들어야 하기 때문이기도 하고, 더 중요한 이유는 각 새로운 데이터
    타입 정의 별로 리스트를 다루는 함수들 ([length], [rev], 등)을 모두
    새로운 버전을 정의해야 하기 때문이다.  
*)

(** 이런 반복을 모두 피하기 위해 콕은 _다형성_ 귀납적 타입을 정의하는
    방법을 지원한다.  예를 들어 _다형 리스트_ 데이터 타입은 다음과
    같다.

*)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

(** 이 정의는 이전 장의 [natlist] 정의와 똑같다. 다만 [cons] 생성자의
    [nat] 인자를 임의의 타입 [X]로 대체하고, [X]에 대한 바인딩을
    헤더에 추가했으며, 생성자들 타입에 [natlist]를 [list X]로 바꾼
    것이 다르다. ([nil]과 [cons] 생성자 이름들을 재사용할 수
    있다. 왜냐하면 [natlist] 정의는 [Module] 정의 안에 있고 이 정의는
    현재 범위 밖에 있기 때문이다.)

    [list]의 실체는 무엇일까? 한 가지 좋은 설명은 [list]는 [Type]에서
    [Inductive] 정의로 매핑하는 _함수_라고 생각하는 것이다. 또는 달리
    설명하자면, [list]는 [Type]에서 [Type]으로 매핑하는 함수라고
    얘기할 수 있다. 어떤 특정 타입 [X]에 대해 [list X] 타입은 타입
    [X]의 원소들로 구성된 리스트들의 집합을 [Inductive](귀납적으로)
    정의한다. *)

Check list.
(* ===> list : Type -> Type *)

(** [list] 정의의 인자 [X]는 생성자 [nil]과 [cons]의 인자가 된다. 즉,
    [nil]과 [cons]는 다형성 생성자로, 이 생성자에 만들고자 하는
    리스트의 타입을 인자로 제공해야 한다. 예를 들어, [nil nat]은 [nat]
    타입의 빈 리스트이다.  *)

Check (nil nat).
(* ===> nil nat : list nat *)

(** 동일한 설명으로, [cons nat]은 [list nat] 타입의 리스트에 [nat]
    타입의 원소를 포함시킨다. 여기 자연수 3만을 포함하는 리스트를
    구성하는 예가 있다.  
*)

Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)

(** [nil]의 타입은 무엇이 될까? 그 정의로부터 [list X] 타입을 읽을 수
    있지만, [list]의 인자인 [X]에 무엇이 바인딩되는지 모른다. [Type ->
    list X]으로 [X]의 의미를 설명할 수 없다. [(X : Type) -> list X]로
    조금 더 설명할 수 있다. 이러한 상황에 대한 콕의 표기법은 [forall X
    : Type, list X]이다.  *)

Check nil.
(* ===> nil : forall X : Type, list X *)

(** 비슷한 상황으로, [cons]의 타입은 그 정의로부터 [X -> list X ->
    list X]로 읽을 수 있다. 하지만 콕의 표기법으로 [X]의 의미를
    설명하자면 [forall X, X -> list X -> list X]이다.
    *)

Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** (표기법에 관한 풀이: .v 파일에서 "forall" 한정자를 문자로
    작성한다. 이 파일로부터 생성한 HTML 파일에서 그리고 다양한
    통합개발환경에서 .v 파일을 보여주는 방식에서 ( 표시 방식을 적절히
    설정하면) [forall]은 흔히 알고 있는 수학의 "뒤집어진 A"로
    표시한다. 하지만 몇 군데에서는 "forall"를 작성하는 것을 여전히
    보게 될 것이다.  이것은 조판 방식의 스타일일 뿐 의미에서는 차이가
    없다.) *)

(** 리스트 생성자를 사용할 때마다 타입 인자를 지정하는 것은 어색한
    부담으로 보일 수도 있지만 이 부담을 줄이는 방법을 곧 알게 될
    것이다. *)

Check (cons nat 2 (cons nat 1 (nil nat))).

(** (여기서 [nil]과 [cons]를 명시적으로 작성해왔는데 그 이유는 새로운
    버전의 리스트에 대해 [ [] ]과 [::] 표기법을 아직 정의하지 않았기
    때문이다. 곧 이 표기법을 정의할 것이다.) *)

(** 이제 돌아가 이전에 작성한 모든 리스트 처리 함수들의 다형성
    버전들을 만들 수 있다.  여기 [repeat]를 예로 보면: *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

(** [nil]과 [cons]에서와 같이 [repeat]를 사용할 때도 우선 타입 인자에
    이 함수를 적용하고 그런 다음 이 타입의 요소(와 숫자)에 적용한다:
    *)

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

(** [repeat]를 다른 종류의 리스트를 만들기 위해 사용하려면 간단히
    적절한 타입 인자를 지정하기만 하면 된다. *)

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity.  Qed.


Module MumbleGrumble.

(** **** 연습문제: 별 두 개 (mumble_grumble)  *)
(** 다음 두 개의 귀납적 정의 타입들을 고려하자.  *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** 어떤 타입 [X]에 대해 [grumble X] 타입의 원소는 다음 중 어느 것인가?
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c]
(* 여기를 채우시오 *)
*)
(** [] *)

End MumbleGrumble.

(* ----------------------------------------------------------------- *)
(** *** 타입 주석 추론 *)

(** [repeat] 정의를 다시 작성해보자. 이번에는 어느 인자의 타입도
    지정하지 않을 것이다.  콕 시스템은 여전히 이 정의를 받아들일까?
    *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** 정말로 받아들인다. 콕은 [repeat']에 어떤 타입을 매겼을지 보자: *)

Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

(** [repeat]와 정확히 동일한 타입이다. 콕은 _타입 유추_를 사용하여
    [X]의 타입, [x]의 타입, [count]의 타입이 무엇이어야 하는지 추론할
    수 있다. 예를 들어, [X]는 [cons]에 대한 인자로서 사용되기 때문에
    [Type]이어야 한다. 왜냐하면 [cons]는 첫 번째 인자로 [Type]을
    기대하기 때문이다. 그리고, [count]를 [0]과 [S]로 매칭 하므로 [nat]
    타입이어야 한다, 등등.

    이 강력한 방법으로 우리는 모든 곳에 타입 주석을 항상 명시적으로
    작성할 필요는 없다.  물론 명시적으로 타입을 작성해놓으면 문서로써
    그리고 제대로 작성되었는지 여부를 검사하는데도 여전히 매우
    유용하다. 여러분의 코드에서 지나치게 많이 타입 주석을 달아놓거나
    (혼란스럽고 산만할 수 있다) 너무 적게 작성하지 않도록 (여러분의
    코드를 이해하기 위해 독자가 머리 속으로 타입 유추를 수행해야 한다)
    적절한 균형을 찾도록 노력해야 한다.
     *)

(* ----------------------------------------------------------------- *)
(** *** 타입 인자 합성 *)

(** 다형 타입 함수를 사용하려면 다른 인자들과 함께 타입 인자들도
    전달해야 한다. 예를 들어, 위의 [repeat] 함수의 몸체에서 재귀
    호출은 타입 [X]를 함께 전달해야 한다. 그러나 [repeat]의 두 번째
    인자는 [X] 타입의 원소이기 때문에 첫 번째 인자는 오직 [X]만
    가능하다는 것은 온전히 명백하다. 따라서 왜 우리가 이 타입 인자
    [X]를 명시적으로 작성해야 하는가?

    다행히도 콕에서는 이런 종류의 중복을 피할 수 있다. 어떠한 타입
    인자 대신 "묵시적 인자" [_]를 작성할 수 있는데, 이 것은 "콕
    시스템에서 스스로 이 자리에 나올 것을 파악하도록 해주세요"라고
    해석할 수 있다. 더 정확히 설명하자면, 콕 시스템에서 [_]를 만날 때
    그 상황에서 사용 가능한 모든 정보를 _통합_할 것이다. 적용하려는
    함수의 타입 다른 인자들의 타입들, 적용을 하는 문맥에서 기대하는
    타입 등등. 그 결과로 [_]를 대체할 구체적인 타입을 결정한다.

    이 타입 인자 합성은 타입 주석 유추와 비슷하게 들릴 수도
    있다. 정말로 이 두 절차는 동일한 방법에 의존한다. 아래처럼 함수의
    어떤 인자들의 타입들을 그냥 생략하는 대신

      repeat' X x count : list X :=

    이 타입들을 [_]로 대체할 수도 있다.
   
      repeat' (X : _) (x : _) (count : _) : list X :=

    이 것은 콕 시스템으로 하여금 빠진 정보를 유추하도록 지시하는
    것이다.

    묵시적 인자들을 사용하면 이 [repeat] 함수를 다음과 같이 작성할 수
    있다: *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(** 이 예에서, [X] 대신 [_]를 작성하기 때문에 그다지 많이 노력을
    줄이지 않는다.  하지만 많은 경우에 키를 누르고 코드를 읽는 면에
    있어서 사소하지 않은 차이를 보인다. 예를 들어 숫자들을 포함하는
    리스트 [1], [2], [3]을 작성하기를 원한다고 가정하자. 이렇게
    작성하는 대신에...  *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...인자 합성을 사용하여 다음과 같이 작성한다:  *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ----------------------------------------------------------------- *)
(** *** 묵시적 인자 *)

(** 한 단계 더 나아가 콕 시스템으로 하여금 주어진 함수의 타입 인자들을
    _항상_ 유추하도록 설정하여 대부분의 경우 [_]를 작성하는 것도 피할
    수도 있다.

    다음의 [Arguments] 지시어를 사용하여 함수 이름을 지정하고 그
    함수의 인자 이름들을 나열한다. 이때 중괄호로 묶인 인자들을 묵시적
    인자로 다루도록 지시한다. (만일 정의의 어떤 인자들에 이름이 없다면
    보통 생성자의 경우 그러한데, 와일드카드 패턴 [_]으로 표시할 수
    있다.)  *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(** 이제 타입 인자들을 전혀 작성할 필요가 없다:  *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(** 또 다른 방법으로, 함수를 선언할 때 어떤 인자를 묵시적이라고 선언할
    수 있다.  해당 인자를 괄호 대신 중괄호로 감싸면 된다. 예를 들어:
    *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(** ([repeat''']의 재귀 호출에 타입 인자를 제공할 필요 조차도 없었음을
     보라.  타입 인자를 제공하면 무효가 될 것이다!)

    앞으로 가능하면 이 스타일을 사용할 것이지만 [Inductive] 생성자들에
    대해서는 명시적으로 [Argument] 선언하는 것을 계속 사용할 것이다.
    그 이유는 귀납적 타입의 인자를 묵시적으로 선언하면 그 타입 자체가
    묵시적이 되기 때문이다. 예를 들어 [list] 타입을 다음과 같이 선언해보자:
    *)

Inductive list' {X:Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.

(** [X]를 [list'] 자체를 포함하는 귀납적 정의 _전체_에 대해 묵시적으로
    선언하기 때문에 [list' nat]이나 [list' bool] 등으로 작성하지
    못하고 단지 [list']로 이제 작성해야 한다. 이것은 의도하지 않게
    지나치게 나아간 것이다.
 *)

(** 이제 새로운 다형 리스트에 관한 두 세 가지 표준 리스트 함수들을
    다시 구현함으로써 마무리짓자... *)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity.  Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** 명시적으로 타입 인자들을 작성하기 *)

(** 때때로 콕 시스템은 타입 인자를 결정하기에 충분한 주변 정보를
    가지고 있지 않은 경우에 [Implicit]로 인자들을 선언할 때 작은
    문제가 발생할 수 있다. 그런 경우에 콕 시스템에 직접 그 인자를 이번
    단 한 번만 지정하기를 원할 필요가 있다. 예를 들어 다음과 같이
    작성하는 경우에: *)

Fail Definition mynil := nil.

(** ([Definition] 앞의 [Fail] 속성은 _어떠한_ 명령어와 함께 사용할 수
    있다.  그 의미는 이 명령어를 실행하면 정말로 실패한다는 것을
    알리는데 사용한다.  만일 이 명령어가 실패하면 콕 시스템은 해당
    에러 메시지를 출력하지만 그 다음을 계속해서 처리한다.)

    여기에서 콕 시스템은 [nil]에 어떤 타입 인자를 제공해야 할지 몰라서
    에러를 낸다. 명시적으로 타입을 선언하여 콕 시스템이 [nil]의
    "적용"에 도달할 때 더 많은 정보를 갖도록 도와줄 수 있다:
 *)

Definition mynil : list nat := nil.

(** 다른 방법으로는 함수 이름 앞에 [@]을 두어 묵시적 인자들을
    명시적으로 작성하도록 강제할 수 있다. *)

Check @nil.

Definition mynil' := @nil nat.

(** 인자 합성과 묵시적 인자를 사용하면 이전과 같이 리스트에 대한
    편리한 표기법을 사용할 수 있다. 생성자 타입 인자들을 묵시적으로
    만들었기 때문에 콕 시스템은 이 표기법을 사용할 때 마다 이 인자들을
    자동으로 유추할 것이다. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** 이제 리스트를 우리가 바라던대로 그대로 작성할 수 있다: *)

Definition list123''' := [1; 2; 3].

(* ----------------------------------------------------------------- *)
(** *** 연습문제 *)

(** **** 연습문제: 별 두 개, 선택 사항 (poly_exercises)  *)
(** 여기 두 세가지 간단한 연습문제가 있다. [Lists] 장에 있는
    연습문제들과 유사한데, 다형성을 가지고 연습하도록 구성되어
    있다. 아래에서 증명을 완성하시오. *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  (* 여기를 채우시오 *) Admitted.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 두 개, 선택 사항 (more_poly_exercises)  *)
(** 다음은 조금 더 흥미로운 연습문제들이다... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 다형성을 갖춘 쌍 *)

(** 동일한 패턴을 따라 지난 장에서 정의했던 숫자 쌍의 타입 정의를 보통
    _곱_이라고 부르는 _다형성을 갖춘 숫자 쌍_으로 일반화 시킬 수 있다: *)

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

(** 리스트에 대해 그랬던 것 처럼 타입 인자들을 묵시적으로 선언하고
    익숙한 표기법을 정의한다. *)

Notation "( x , y )" := (pair x y).

(** [Notation] 방법으로 곱 _타입_의 표준 표기법을 정의할 수도 있다: *)

Notation "X * Y" := (prod X Y) : type_scope.

(** ([: type_scope] 주석은 콕 시스템에게 이 축약 표기는 타입을 파싱할
    때 사용되기만 해야 한다고 알려준다. 이렇게 해야 곱셈 기호와 충돌을
    피한다.) *)

(** 처음에는 [(x,y)]와 [X*Y]를 혼동할 수 있다. [(x,y)]는 두 개의 다른 값들을 
    조합해서 만든 _값_이고 [X*Y]는 두 개의 다른 타입들로 만든 _타입_이다. 
    만일 [x]가 [X] 타입이고 [y]가 [Y] 타입이면 [(x,y)]는 [X*Y] 타입이다. *)

(** 첫 번째 원소와 두 번째 원소를 꺼내는 함수들은 이제 어떠한 함수형
    프로그래밍 언어에서 있는 것과 상당히 비슷하게 보인다. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** 다음 함수는 두 개의 리스트들을을 받아 쌍들의 리스트로
    조합한다. 다른 함수형 언어에서 종종 [zip]이라 부르는데, 우리는 콕
    표준 라이브러리와의 일관성을 위해 [combine]이라 부른다. *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(** **** 연습문제: 별 한 개, 선택 사항 (combine_checks)  *)
(** 다음 질문들에 대한 답을 종이 위에 작성해 답해보고 콕 시스템으로 그 답을
    검사해보시오:
    - [combine]의 타입은 무엇인가 (즉, [Check @combine]으로 
      무엇을 출력하는가?)
    - 아래 명령은 무엇을 출력하는가?

        Compute (combine [1;2] [false;false;true;true]).
 *)

(** [] *)

(** **** 연습문제: 별 두 개, 추천 (split)  *)

(** 함수 [split]은 [combine]의 오른쪽 역 함수이다. 쌍들의 리스트를
    받아 리스트들의 쌍을 리턴한다. 많은 함수형 언어에서 [unzip]이라
    부른다.

    아래에서 [split]의 정의를 채우시오. 반드시 주어진 단위 테스트를
    통과하도록 확인하시오. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
  (* 이 줄을  ":= _당신의 정의_ ."로 바꾸시오 *). Admitted.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* 여기를 채우시오 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 다형성을 갖춘 선택 *)

(** 일단 마지막 다형 타입: _다형성을 갖운 선택_,은 이전 장에서
    [natoption]을 일반화한 것이다: *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

(** [nth_error] 함수를 어떤 타입의 리스트에 대해서도 동작하도록 이제
    다시 작성할 수 있다. *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(** **** 연습문제: 별 한 개, 선택사항 (hd_error_poly)  *)
(** 이전 장의 [hd_error] 함수의 다형성을 갖춘 버전을 완성하시오. 아래에
    있는 단위 테스트들을 모두 통과하도록 확인하시오. *)

Definition hd_error {X : Type} (l : list X) : option X
  (* 이 줄을 ":= _당신의 정의_ ."로 대체하시오. *). Admitted.

(** 다시 한 번, 묵시적 인자들을 강제로 명시적으로 작성하게 만들려면 그
    함수 이름 앞에 [@]을 사용할 수 있다. *)

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
 (* 여기를 채우시오 *) Admitted.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
 (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 데이터로서 함수 *)

(** 모든 함수형 언어들 (ML, Haskell, Scheme, Scala, Clojure, 등)을
    포함한 많은 다른 현대 프로그래밍 언어와 같이 콕 시스템은 함수들을
    일등 시민으로 다룬다. 즉, 함수들을 다른 함수들의 인자로 전달하고
    그 결과로 리턴하며 자료 구조에 저장하는 등등.  *)

(* ================================================================= *)
(** ** 고차원 함수 *)

(** 다른 함수들을 다루는 함수들은 보통 _고차원_ 함수라 부른다. 여기
    간단한 고차원 함수가 있다: *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** 여기 인자 [f]는 그 자체로 함수 ([X]에서 [X]로
    매핑하는)이다. [doit3times]의 몸체에서 [f]를 어떤 값 [n]에 세 번
    적용한다.  *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ================================================================= *)
(** ** 필터(Filter) *)

(** 여기 더 유용한 고차원 함수가 있다. [X] 타입의 리스트와 [X]에 관한
    _술어_([X]를 [bool]로 매핑하는 함수)를 받아 그 리스트를
    "필터링"하고 이 술어가 [true]인 원소들만을 포함하는 새로운
    리스트를 리턴한다. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** 예를 들어, [filter]를 술어 [evenb]와 숫자 리스트 [l]에 적용하면
    [l]의 짝수들만을 포함하는 리스트를 리턴한다.  *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** [Lists] 장에서 정의한 [countoddmembers]을 [filter]를 사용하여
    간단하게 정의할 수 있다. *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ================================================================= *)
(** ** 이름이 없는 함수 *)

(** 바로 위 예제에서 단지 [filter]의 인자로 전달하기 위해서 함수
    [length_is_1]을 정의하고 이름을 붙여야 하는 것은 거의 틀림없이
    약간 슬픈 일이다. 왜냐하면 이 함수는 결코 다시 사용하지 않을
    것이기 때문이다. 더우기 이것은 단발성 예제가 아니다. 고차원
    함수들을 사용할 때 다시 사용하지 않을 "단발성" 함수들을 인자들로
    전달하기를 원할 것이다. 이런 함수들에 이름을 지어야 하는 것은 매우
    번거로운 일이 될 것이다.

    다행히도 더 나은 방법이 있다. 함수를 상위 레벨에서 선언하거나
    이름을 붙이지 않고 "즉석으로" 함수를 만들 수 있다. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(** 식 [(fun n => n * n)]은 "주어진 숫자 [n]으로 부터 [n * n]을 내는
    함수"로 읽을 수 있다. *)

(** 여기 [filter] 예제가 있다. 이름 없는 함수를 사용해서 다시
    작성하였다. *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** **** 연습문제: 별 두 개 (filter_even_gt7)  *)
(** ([Fixpoint] 대신) [filter]를 사용해서 콕 함수 [filter_even_gt7]을
    작성하시오. 이 함수는 입력으로 자연수 리스트를 받아 짝수이면서
    7보다 큰 숫자들만으로 이루어진 리스트를 리턴한다. *)

Definition filter_even_gt7 (l : list nat) : list nat
  (* 이 줄을 ":= _당신의 정의_ ."로 바꾸시오 *). Admitted.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* 여기를 채우시오 *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개 (partition)  *)
(** [filter]를 사용하여 콕 함수 [partition]을 작성하시오:

      partition : forall X : Type, (X -> bool) -> list X -> list X *
                  list X

   집합 [X], 타입 [X -> bool]의 테스트 함수와 [list X]가 주어지면
   [partition]은 리스트들의 쌍을 리턴한다. 이 쌍의 첫 번째 원소는 원래
   리스트의 서브 리스트로 그 테스트를 만족하는 원소들을 포함한다. 두
   번째 원소는 이 테스트에 실패한 원소들을 포함하는 서브
   리스트이다. 두 서브리스트들의 원소들의 순서는 원래 리스트에서
   순서와 동일해야 한다. *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  (* 이 줄을 ":= _당신의 정의_ ."로 대체하시오 *). Admitted.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* 여기를 채우시오 *) Admitted.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
(* 여기를 채우시오 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 맵(Map) *)

(** 또 다른 편리한 고차원 함수 [map]이 있다. *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** 함수 [f]와 리스트 [ l = [n1, n2, n3, ...] ]을 받아 리스트 [ [f n1,
    f n2, f n3,...] ]을 리턴한다. 이 리스트는 [f]를 [l]의 각 원소에
    차례로 적용한 결과이다. 예를 들어: *)

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** 입출력 리스트의 원소 타입들은 동일할 필요가 없다. 그래서 [map]은
    _두 개_의 타입 인자들 [X]와 [Y]를 받는다. 맵 함수는 숫자 리스트와
    숫자를 부울 값으로 매핑하는 함수에 적용하면 부울 값 리스트를 낼 수
    있다: *)

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

(** 맵 함수는 숫자 리스트와 숫자를 _부울 리스트들_로 매핑하는 함수에
    적용해서 부울 _리스트들의 리스트_를 낼 수 있다: *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** 연습문제들 *)

(** **** 연습문제: 별 세 개 (map_rev)  *)
(** [map]과 [rev]의 교환 법칙을 보여준다. 보조 정리를 새로 정의할 필요가
    있다. *)

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 두 개, 추천 (flat_map)  *)
(** 함수 [map]은 [X -> Y] 타입의 함수를 사용하여 [list X]의 원소를
    [list Y] 원소로 매핑한다. 이와 비슷한 함수 [flat_map]을 정의하여
    [X -> list Y] 타입의 함수 [f]를 사용하여 [list X]의 원소를 [list
    Y]의 원소로 매핑한다. 이 함수의 정의는 아래와 같이 [f]의 결과를
    '펼치면서' 동작해야 한다:

        flat_map (fun n => [n;n+1;n+2]) [1;5;10] = [1; 2; 3; 5; 6; 7;
      10; 11; 12].  *)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y)
  (* 이 줄을  ":= _당신의 정의_ ."로 대체하시오 *). Admitted.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* 여기를 채우시오 *) Admitted.
(** [] *)

(** 리스트는 [map] 함수로 다룰 수 있는 유일한 귀납적 타입이 아니다.
    [option] 타입에 대한 [map] 함수는 이렇게 정의할 수 있다: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** 연습문제: 별 두 개, 선택사항 (implicit_args)  *)
(** [filter]와 [map]를 정의하고 사용할 때 많은 곳에서 묵시적 인자들을
    사용한다.  묵시적 인자들 주위의 중괄호들을 괄호로 바꾸고 필요한
    곳에 명시적으로 타입 인자들을 채운다. 콕 시스템을 사용하여 제대로
    바꾸었음을 확인하시오. (이 연습문제의 답은 제출하지 않는다. 이
    파일을 _복사_해서 연습문제를 풀고 나중에 버리는 것이 분명히 가장
    쉬울 것이다.)  *)
(** [] *)

(* ================================================================= *)
(** ** 접기(Fold) *)

(** 훨씬 더 강력한 고차원 함수 [fold]가 있다. 이 함수는 구글의
    맵/리듀스 분산 프로그래밍 프레임워크의 핵심에서 사용하는
    "[reduce]" 연산을 위한 영감을 제공한다.  *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** 직관적으로 [fold] 연산의 동작은 주어진 이진 연산 [f]를 주어진 리스트의 원소들의
    각 쌍에 적용하는 것이다. 예를 들어 [ fold plus [1;2;3;4] ]는 직관적으로 
    [1+2+3+4]가 된다. 자세히 설명하면, [f]에 대한 초기 두 번째 입력으로 사용할
    "시작 원소"도 필요하다. 예를 들어,

       fold plus [1;2;3;4] 0

    는 아래 결과를 낸다:

       1 + (2 + (3 + (4 + 0))).

    몇 가지 추가 예제들: *)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(** **** 연습문제: 별 한 개, 고급 (fold_types_different)  *)
(** [fold]의 타입은 _두 개_의 타입 변수들 [X]와 [Y] 패러미터로
    구성되어 있고, 인자 [f]는 [X]의 원소와 [Y]의 원소를 받아 [Y]의
    원소를 리턴하는 이진 연산이다. [X]와 [Y]와 다르면 유용한 상황이
    무엇일지 생각해보시오.  *)

(* 여기를 채우시오 *)
(** [] *)

(* ================================================================= *)
(** ** 함수를 만드는 함수 *)

(** 지금까지 이야기한 대부분의 고차원 함수들은 함수들을 인자로 받는
    것이었다. 다른 함수들의 결과로 함수들을 _리턴_하는 몇 가지 예제를
    살펴보자. 우선 (어떤 타입 [X]의) 값 [x]를 받고 [nat]에서 [X]로
    매핑하는 그래서 [x]를 내는 함수를 리턴하는 함수가 여기 있다.
    [nat] 인자는 무시한다. *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** 사실 이미 살펴본 다중 인자 함수들은 함수들을 데이터로 전달하는
    예제이기도 하다.  그 이유를 살펴보기 위해 [plus] 타입을 다시
    생각해본다. *)

Check plus.
(* ==> nat -> nat -> nat *)

(** 이 식에서 각 [->]은 실제로 타입에 대한 _이진_ 연산이다. 이 것은
    _우측으로 묶인_ 연산이다. 그래서 [plus]의 타입은 정말로 [nat ->
    (nat -> nat)]을 짧게 줄인 것이다. 즉, "[plus]는 단일 인자 함수로
    [nat]의 값을 받고 또 다른 단일 인자 함수를 리턴한다. 이 함수는
    [nat]의 값을 받아 [nat]의 값을 리턴한다"이다.  위 예제에서 항상
    [plus]를 한번에 두 개의 인자에 적용했지만 원한다면 단지 첫 번째
    인자만 줄 수 있다. 이러한 함수 사용을 _부분 적용_이라 부른다. *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ################################################################# *)
(** * 추가 연습문제들 *)

Module Exercises.

(** **** 연습문제: 별 두 개 (fold_length)  *)
(** 리스트에 대한 많은 공통 함수들은 [fold]를 이용해서 구현할 수 있다.
    예를 들어, [length]를 이렇게 정의할 수도 있다: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(** [fold_length]의 정확성을 증명하시오. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
(* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개 (fold_map)  *)
(** [fold]를 사용하여 [map]도 정의할 수 있다. 아래의 [fold_map]을
    마무리 지으시오. *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y
  (* 이 줄을 ":= _당신의 정의_ "로 대체하시오. *). Admitted.

(** [fold_map]의 정확성을 기술하는 [fold_map_correct] 정리를 콕으로
    작성하고 증명하시오. *)

(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 두 개, 고급 (currying)  *)
(** 콕에서 함수 [f : A -> B -> C]는 실제로 [A -> (B -> C)]
    타입이다. 즉, [f]에 [A] 타입의 값을 주면 함수 [f' B -> C]를 낼
    것이다. [f']에 [B]를 주면 [C] 타입의 값을 리턴할 것이다. 이런
    방식으로 [plus3]에서 처럼 부분 적용을 사용한다. 일련의 인자들을
    함수를 리턴하는 함수로 처리하는 것을 _커링_이라 부른다. 논리학자
    하스켈 커리(Haskell Curry)의 이름을 따서 붙인 것이다.

    역으로 [A -> B -> C] 타입을 [(A * B) -> C]로 해석할 수 있다.  이
    것을 _언커링_이라 부른다. 언커링 이진 함수에는 두 인자들을 쌍으로
    한 번에 주어야 한다. 부분 적용을 허용하지 않는다. *)

(** 다음과 같이 커링을 정의할 수 있다: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** 연습문제로 이 것의 역 [prod_uncurry]을 정의하시오. 그런 다음 이 두
    가지가 서로 역이라는 것을 보이는 정리들을 아래에서 증명하시오. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  (* 이 줄을 ":= _당신의 정의_ "로 대체하시오. *). Admitted.

(** 커링이 유용한 (사소한) 예로써 위에서 본 예제들 중 하나를 짧게 하기
    위해 커링을 사용할 수 있다: *)

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** 사고 단련: 다음 명령어들을 실행하기 전에 [prod_curry]와
    [prod_uncurry]의 타입들을 계산해보자. *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 두 개, 고급 (nth_error_informal)  *)
(** [nth_error] 함수의 정의를 생각해보자:

   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
     end.

   다음 정리를 비형싲거으로 증명해보시오:

   forall X n l, length l = n -> @nth_error X l n = None

(* 여기를 채우시오 *)
*)
(** [] *)

(** **** 연습문제: 별 네 개, 고급 (church_numerals)  *)
(** 이 연습문제는 수학자 알론조 처치 이름을 따서 _처치 숫자_라고
    부르는 자연수를 정의하는 한 가지 방법을 탐구한다. 자연수 [n]을
    함수 [f]를 인자로 받고 [f]를 [n]번 반복하는 함수로 표현할 수
    있다. *)

Module Church.
Definition nat := forall X : Type, (X -> X) -> X -> X.

(** 이 표기법으로 몇 가지 숫자를 작성하는 법을 살펴보자. 함수를 한 번
    반복하는 것은 적용하는 것과 동일해야 한다. 그래서: *)

Definition one : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** 비슷하게 [two]는 [f]를 그 인자에 두 번 적용해야 한다: *)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** 다소 교묘하게 [zero]를 정의한다. 어떻게 "함수를 0번 적용"할 수
    있을까?  그 답은 실제로 간단하다. 그냥 인자를 건드리지 않고
    반환하면 된다. *)

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** 더 일반적으로 숫자 [n]을 [fun X f x => f (f ... (f x) ...)]로
    [f]가 [n]번 나타나도록 작성할 수 있다. 특히 이전에 정의했던
    [doit3times] 함수가 실제로 [3]의 처치 표현임을 주목하라. *)

Definition three : nat := @doit3times.

(** 다음 함수들의 정의를 완성하시오. 해당하는 단위 테스트들을
    통과하는지 [reflexivity] 로 증명해서 확인하시오.  *)

(** 다음 자연수: *)

Definition succ (n : nat) : nat
  (* 이 줄을 ":= _당신의 정의_ "로 대체하시오 *). Admitted.

Example succ_1 : succ zero = one.
Proof. (* 여기를 채우시오 *) Admitted.

Example succ_2 : succ one = two.
Proof. (* 여기를 채우시오 *) Admitted.

Example succ_3 : succ two = three.
Proof. (* 여기를 채우시오 *) Admitted.

(** 두 자연수에 대한 덧셈: *)

Definition plus (n m : nat) : nat
  (* 이 줄을 ":= _당신의 정의_ "로 대체하시오 *). Admitted.

Example plus_1 : plus zero one = one.
Proof. (* 여기를 채우시오 *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* 여기를 채우시오 *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* 여기를 채우시오 *) Admitted.

(** 곱셈: *)

Definition mult (n m : nat) : nat
  (* 이 줄을 ":= _당신의 정의_ "로 대체하시오 *). Admitted.

Example mult_1 : mult one one = one.
Proof. (* 여기를 채우시오 *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* 여기를 채우시오 *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* 여기를 채우시오 *) Admitted.

(** 누승: *)

(** (_힌트_: 다형성은 여기서 중요한 역할을 담당한다. 그러나 반복할
    적절한 타입을 선택하는 것이 까다롭다. 만일 "Universe
    inconsistency" 에러를 만나면 다른 타입에 대해 반복할 것을
    시도해보시오: [nat] 자체는 대체로 여러 문제가 있다.) *)

Definition exp (n m : nat) : nat
  (* 이 줄을 ":= _당신의 정의_ "로 대체하시오 *). Admitted.

Example exp_1 : exp two two = plus two two.
Proof. (* 여기를 채우시오 *) Admitted.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. (* 여기를 채우시오 *) Admitted.

Example exp_3 : exp three zero = one.
Proof. (* 여기를 채우시오 *) Admitted.

End Church.
(** [] *)

End Exercises.

(** $Date: 2017-09-06 11:44:36 -0400 (Wed, 06 Sep 2017) $ *)

