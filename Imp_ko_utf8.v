(** * Imp: 간단한 명령형 언어 *)

(** 이 장에서 콕 밖에 있는 흥미로운 것을 콕으로 공부하는 방법을 더
    진지하게 살펴볼 것이다. 우리의 사례 연구는 C와 Java와 같은 보통의
    주류 언어의 작은 핵심 부분을 포함하는 _간단한 명령형 프로그래밍
    언어_로 Imp라 부른다. 여기 잘 알고 있는 수학 함수를 Imp로
    작성해본다.

     Z ::= X;; Y ::= 1;; WHILE not (Z = 0) DO Y ::= Y * Z;; Z ::= Z -
     1 END *)

(** 이 장에서 Imp의 _구문_과 _의미_를 정의하는 법을
    살펴본다. _프로그래밍언어 기초_의 추가 장들에서 (_소프트웨어
    기초_, 2권) _프로그램 동치_ 이론을 제시하고, 명령형 프로그램을
    추론하는데 널리 사용하는 논리 _호어 논리_를 소개한다. *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

From LF Require Import Maps.

(* ################################################################# *)
(** * 산술식과 부울식 *)

(** Imp를 세가지 부분으로 나누어 소개한다. 우선 _산술식과 부울식_의
    핵심 언어 그 다음 _변수_를 도입하여 확장하고 마지막으로 할당문,
    조건문, 순차문, 반복문을 포함한 _명령어_ 언어 부분으로 나눈다. *)

(* ================================================================= *)
(** ** 구문 *)

Module AExp.

(** 아래 두 정의는 산술식과 부울식의 _추상 구문_을 규정한다. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(** 이 장에서 프로그래머가 실제로 작성하는 실제 구문에서 이 추상 구문
    트리로 변환하는 것을 생략할 것이다. 이 과정은 예를 들어 문자열
    ["1+2*3"]을 다음 AST로

      APlus (ANum 1) (AMult (ANum 2) (ANum 3)).

    변환할 것이다.

    선택 사항인 [ImpParser]장에서 이러한 변환을 할 수 있는 간단한 어휘
    분석과 구문 분석 구현한다. 이 구현 방법을 이해학 위해서 해당 장을
    이해할 필요는 _없다_. 하지만 이 기법을 다루는 강의를 듣지 않았다면
    (예: 컴파일러 과목) 자세히 읽지 않아도 된다. *)

(** 비교를 위해 여기 동일한 추상 구문을 정의하는 
    전통적인 BNF (Backus-Naur Form) 문법이 있다.

    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | not b
        | b and b
*)

(** 위의 콕 버전과 비교하면...

       - 이 BNF는 더 비형식적이다. 예를 들어 식의 표면적인 구문이 약간
         남아 있다. 덧셈 연산은 [+]으로 작성하고 중위 기호라는 것을 알
         수 있지만 어휘 분석과 구문 분석의 다른 면은 생략하고
         있다. 예를 들어 [+], [-], [*]의 상대적인 우선순위는 표현되어
         있지 않다. 컴파일러를 구현할 때와 같이 이 구문을 형식적인
         정의로 바꾸려면 추가적인 정보(와 인간 지능)이 필요할 수 있다.

         콕 버전은 일관되게 이런 모든 정보를 생략하고 추상 구문에만
         집중한다.

       - 반면에 BNF 버전은 더 간단하고 읽기 쉽다. 이 버전의 비형식적인
         면은 표현이 유연하고, 일반적인 아이디어를 전달하는 것이 모든
         상세한 내용을 정밀하게 정의하는 것 보다 중요한 칠판에서
         토의와 같은 상황에서 큰 장점이 있다.

         정말로 BNF 같은 표기법이 십여개 있고 이 표기법을 자유롭게
         바꾸어 사용한다.  사용하는 BNF 형식이 무엇인지 말하지 않는데
         그럴 필요도 없기 때문이다. 대강 준비된 비형식적으로 이해하는
         것이 바로 중요한 것이다.

    두 가지 종류의 표기법, 즉 사람과 얘기할 때 비형식적인 표기법을,
    구현하고 증명할 때 형식적인 표기법에 편해지는 것이 좋다. *)

(* ================================================================= *)
(** ** 계산 *)

(** 산술식을 _계산_하여 숫자를 낸다. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** 비슷하게 부울식을 계산하면 부울값을 얻는다. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => leb (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ================================================================= *)
(** ** 최적화 *)

(** 아직 그다지 많이 정의하지 않았지만 벌써 이 정의들을 이용할 수
    있다.  산술식을 취해서 [0+e]가 나타나면 [e]로 간략화하는 함수를
    가정하자 (예를 들어, [(APlus (ANum 9) e])을 [e]로). *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(** 이 최적화 방법이 올바른지 몇가지 예제를 가지고 테스트해서 그
    결과가 OK인지 볼 수 있다. *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(** 이 최적화가 정확한지 (즉, 최적화된 식을 계산하면 원래 식과 동일한
    결과를 내는지)를 확신하고 싶으면 증명해야 한다. *)

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1.
    + (* a1 = ANum n *) destruct n.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* ################################################################# *)
(** * 콕 자동화 *)

(** 위 증명에서 조금 짜증나는 수준으로 반복되는 패턴이
    나타난다. 산술식 언어나 증명하려는 최적화가 상당히 더 복잡하다면
    정말 큰 문제가 될 것이다.

    이제까지 적은 수의 콕 전술만 사용해서 증명해왔다. 증명의 일부를
    자동으로 만들어내는 강력한 기능을 완전히 무시했다. 이 절에서 이런
    기능들을 몇 가지 소개하고 다음 장들에서 더 보게 될 것이다.  콕의
    자동화는 강력한 도구이고 이 자동 증명 기능에 익숙해지려면 노력이
    필요하다. 하지만 일단 익숙해지면 우리의 능력을 확장시켜서 더
    복잡한 정의와 더 흥미로운 성질들까지 지루하거나 반복적이거나
    상세한 내용에 압도되지 않고 증명하도록 만들 것이다. *)

(* ================================================================= *)
(** ** 고차원 전술(Tacticals) *)

(** _고차원 전술_은 다른 전술을 인자로 받는 전술에 대한 콕 용어다.  *)

(* ----------------------------------------------------------------- *)
(** *** [try] 고차원 전술 *)

(** 만일 [T]가 전술이면 [try T]는 [T]처럼 동작하는 전술로 한가지
    예외는 [T]가 실패하면 [try T]는 (실패하는 대신) _성공적으로_ 전혀
    아무것도 하지 않는다. *)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does [reflexivity] *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* [reflexivity]만 실패할 것이다. *)
  apply HP. (* 다른 방법으로 이 증명을 여전히 마무리지을 수 있을 것이다. *)
Qed.

(** 위와 같은 모두 수동 증명인 경우에 [try]를 사용할 이유가 없지만
    다음에 보게 되듯이, [;] 고차원 전술과 함께 증명을 자동화하는 것이
    매우 유용하다. *)

(* ----------------------------------------------------------------- *)
(** *** [;] 고차원 전술 (간단한 형태) *)

(** 가장 흔한 형태로 [;] 고차원 전술은 두 전술을 인자로 받는다. 복합
    전술 [T; T']은 먼저 [T]를 실행하고 [T]에 의해 생성된 _각 부분
    목적_에 그 다음 [T']을 실행한다. *)

(** 예를 들어, 다음 간단한 보조 정리를 보자. *)

Lemma foo : forall n, leb 0 n = true.
Proof.
  intros.
  destruct n.
    (* 동일하게 증명될 두 부분 목적을 남긴다...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** 이 증명을 [;] 고차원 전술을 사용하여 간단하게 만들 수 있다. *)

Lemma foo' : forall n, leb 0 n = true.
Proof.
  intros.
  (* 현재 목적을 [destruct] *)
  destruct n;
  (* 그 다음 생성된 각 부분 목적을 [simpl]  *)
  simpl;
  (* 그리고 생성된 부분 목적에 [reflexivity]을 적용 *)
  reflexivity.
Qed.

(** [try]와 [;]를 함께 사용하여 조금 전에 반복되는 패턴이 나타나
    증명하기 귀찮았던 증명에서 이 반복 패턴을 제거할 수 있다. *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* 대부분의 경우 IH로 증명하고... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... 남은 경우 ANum과 APlus는 다르다. *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1;
      (* 다시 한번 대부분의 경우 IH로 증명하고 *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* 흥미로운 경우는 [e1 = ANum n]일 때인데 [try...]가 아무 효과가 
       없다. 이 경우 [n]을 생성자 별로 나누어 최적화가 적용가능한지 보고
       귀납적 가정을 가지고 부분 목적을 다시 작성해서 변형해야 한다.  *)
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity.   Qed.

(** 콕 전문가는 [induction]같은 전술 다음에 많은 유사한 경우를 한번에
    다 증명하기 위해 "[...; try...]"와 같은 관용 표현을 자주 사용한다.
    자연스럽게 비형식적 증명에서도 이런 행위와 비슷한 것이 있다. 예를
    들어, 최적화 정리에 대한 형식적 증명의 구조와 일치하는 비형식적
    증명이 여기 있다.

    _정리_: 모든 산술식 [a]에 대하여,

       aeval (optimize_0plus a) = aeval a.

    _증명_: [a]에 대한 귀납법에 의하여, 대부분의 경우 IH에 의해
    증명한다. 남은 경우는 다음과 같다.

      - 어떤 [n]에 대해 [a = ANum n]를 가정하자. 다음을 보여야 한다:

          aeval (optimize_0plus (ANum n)) = aeval (ANum n).

        [optimize_0plus]의 정의로부터 바로 증명 가능하다.

      - 어떤 [a1]과 [a2]에 대해 [a = APlus a1 a2]를 가정하자. 다음을
        보여야 한다:

          aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).

        [a1]의 가능한 형태들을 살펴보자. 대부분의 경우
        [optimize_0plus]는 부분식을 가지고 재귀적으로 자기 자신을 
        호출할 뿐이고 [a1]과 동일한 형태의 새로운 식을 다시 만든다. 이러한
        경우 IH에 의해 바로 증명할 수 있다.

        흥미로운 경우는 어떤 [n]에 대해 [a1 = ANum n]일 때이다. 만일 [n = 0]이면

          optimize_0plus (APlus a1 a2) = optimize_0plus a2

        그리고 [a2]에 대한 IH는 정확히 우리가 필요한 것이다. 반면에 어떤 [n']에 대해
        [n = S n']이라면 다시 [optimize_0plus]는 재귀적으로 자기 자신을 
        호출할 뿐이고 그 결과는 IH에 의해 증명된다. [] *)

(** 하지만 이 증명은 여전히 개선될 여지가 있다. (a = ANum n)인 첫번째
    경우 매우 간단하다. 언급했던 IH를 따를 뿐인 경우들보다 훨씬 더
    간단하다. 하지만 이 증명을 상세하게 작성하기로 결정했다. 아마도
    처음부터 이러한 상세 증명을 버리고 "대부분의 경우 IH로부터 바로
    또는 직접적으로 증명가능하다. 오직 흥미로운 경우는 [APlus]에 대한
    경우이다..."고 언급만 한다면 더 좋고 명확한 증명이 될 것이다.
    우리의 형식적 증명에서도 동일하게 개선할 수 있다. 이러한 내용을
    여기에서 설명한다. *)

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* 대부분의 경우 IH에 의해 직접 증명 가능하거나 *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... 또는 정의에 의해 바로 증명 가능하다 *)
    try reflexivity.
  (* 흥미로운 경우는 a = APlus a1 a2일 때이다. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** [;] 고차원 전술 (일반적인 형태) *)

(** [;] 고차원 전술도 위에서 살펴본 [T;T']보더 더 일반적인 형태를 갖는다.
    주어진 전술 [T], [T1], ..., [Tn]에 대해 

      T; [T1 | T2 | ... | Tn]

    는 [T]를 먼저 실행한 다음 [T]로 생성한 첫번째 부분 목적에 [T1]을 실행하고 
    두번째 부분 목적에 [T2]를 실행하고, 등등. 

    그래서 [T;T']는 모든 [Ti]가 동일한 전술인 경우를 위한 특별한 표기법일 뿐이다.
    즉, [T;T']는 다음 표현의 축약형이다:

      T; [T' | T' | ... | T']
*)

(* ----------------------------------------------------------------- *)
(** *** [repeat] 고차원 전술 *)

(** [repeat] 고차원 전술은 다른 전술을 받아 반복해서 적용하다 전술
    적용이 실패하면 멈춘다. 다음은 repeat를 사용하여 긴 리스트에
    [10]이 포함되어 있는지 보여주는 예제이다. *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(** [repeat T] 전술은 결코 실패하지 않는다. 만일 전술 [T]가 원래
    목적에 적용되지 않으면 repeat는 여전히 성공한 것으로 간주하되 원래
    목적을 변경하지 않는다. 즉, 0번 반복한다. *)

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(** 전술 [repeat T]도 [T]를 적용하는 횟수에 어떠한 상한선도 없다. 항상
    성공하는 전술 [T]라면 영원 반복할 것이다. 예를 들어, [simpl]은
    항상 성공하기 때문에 [repeat simpl]은 영원히 반복한다. 콕 언어
    Gallina에서 모든 계산은 종료하는 것이 보장되는 반면 전술을 적용할
    때의 계산은 그렇지 않다! [repeat]와 다른 전술이 하는 일은 콕으로
    하여금 증명을 만드는 것을 가이드하는 것이기 때문에 전술의 비종료
    가능성으로 콕의 논리적 일관성이 지켜지지 않는 영향을 주지 않는다.
    증명을 만드는 과정이 무한히 끝나지 않으면 이것은 단지 증명을
    만드는데 실패했다는 것을 뜻하지 잘못된 증명을 만들었다는 것은
    아니다. *)

(** **** 연습문제: 별 세 개 (optimize_0plus_b)  *)
(** [optimize_0plus] 변환은 [aexp] 값을 변경하지 않기 때문에 [bexp]의
    값을 변경하지 않고 [bexp]에 나타난 모든 [aexp]에 적용할 수 있어야
    한다. [bexp]에 대한 변환을 실행하는 함수를 작성하고 이 변환이
    건전함을 증명하시오.  우리가 살펴본 고차원 전술만 사용해서 이
    증명을 최대한 우아하게 만들어보시오. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp
  (* 이 줄을 당신의 정의로 바꾸시오 *). Admitted.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 네 개, 선택사항 (optimizer)  *)
(** _설계 연습문제_: [optimize_0plus] 함수로 구현한 최적화는 산술식과
    부울식에 관한 많은 방법들 중 한가지일뿐이다.  더 복잡한 최적화를
    작성하고 정확성을 증명해보시오. 작은 것부터 시작해서 (한가지 간단한 최적화를 추가해서
    정확성을 증명하기) 점차 더 흥미로운 것을 쌓아보는 것이 가장 쉬울 것이다.

(* 여기를 채우시오 *) *)
(** [] *)

(* ================================================================= *)
(** ** 새로운 전술 표기법을 정의하기 *)

(** 콕은 전술 스크립트를 "프로그래밍"하는 여러가지 방법도 제공한다.

    - 아래에 예시로 든 [Tactic Notation] 관용어는 여러 전술들을 하나의
      명령어로 묶는 "축약된 전술"을 정의하는 쉬운 방법이다.

    - 더 복잡한 프로그래밍을 위해서 콕은 [Ltac]이라 부르는 내장된
      언어를 제공하고 이 언어에 포함된 기본 연산들로 증명 상태를
      살펴보고 수정할 수 있다. 상세한 내용은 꽤 너무 복잡해서 여기에서
      다룰 수 없다 (그리고 [Ltac]은 콕 설계에서 가장 아름다운 부분은
      아니라고 일반적으로 생각한다!). 하지만 참고 매뉴얼과 콕에 관한
      다른 책에서 [LTac]의 상세 내용을 확인할 수 있다. 콕 표준
      라이브러리에 [Ltac] 정의의 많은 예가 있고 예로 사용할 수 있다.

    - OCaml API도 있어서 낮은 수준에서 콕 내부 구조를 접근하는 전술을
      만들때 사용할 수 있다. 하지만 일반 콕 사용자를 위해서는 이
      어려움을 극복할만한 가치가 거의 없다.

    [Tactic Notation]은 전술을 정의하는 가장 쉬운 방법이다. 다양한
    목적을 위해 많은 기능을 제공한다. 여기 예가 있다. *)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(** [simpl_and_try]라 부르는 새로운 고차원 전술을 정의한다. 전술 [c]를
    인자로 받고 [simpl; try c] 전술과 똑같이 동작하도록 정의한다.
    이제 "[simpl_and_try reflexivity.]"를 쓰면 증명에서 "simpl; try
    reflexivity.]"처럼 동작할 것이다.  *)

(* ================================================================= *)
(** ** [omega] 전술 *)

(** [omega] 전술은 _Presburger arithmetic_이라 부르는 1차 논리 일부에
    대한 판단 절차를 구현한다. Willaim Pugh [Pugh 1991]에 의해 1991년
    발명한 오메가 알고리즘에 기초한다.

    목적이 보편적인 한정사로 한정된 식이고 다음 요소로 구성되어 있다면

     - 숫자 상수, 덧셈 ([+]와 [S]), 뺄셈 ([-]와 [pred]), 상수 곱셈 (이
       것이 프레스버거 산술식이다),

     - 등식 ([=]과 [<>])과 순서 ([<=])와

     - 논리 연결자 [/\], [\/], [~], and [->],

    [omega]를 실행하면 이 목적을 풀거나 또는 사실 거짓이라고 답해줄
    것이다. *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(** (파일 시작 부분에 [Require Import Coq.omega.Omega.]를 보시오. *)

(* ================================================================= *)
(** ** 두세 가지 편리한 전술들 *)

(** 마지막으로 편리한 몇 가지 기타 전술이 있다.

     - [clear H]: 문맥에서 가정 [H]를 삭제.

     - [subst x]: [x = e]나 [e = x] 가정을 문맥에서 찾아 문맥과 현재
       목적에서 [x]를 [e]로 대체하고 가정을 지운다.

     - [subst]: [x = e]나 [e = x] 형태의 _모든_ 가정을 대체한다.

     - [rename... into...]: 증명 문맥에서 가정의 이름을 변경한다.
       예를 들어 이 문맥에 변수 [x]가 있으면 [rename x into y]는 [x]가
       나타난 곳에을 모두 [y]로 변경할 것이다.

     - [assumption]: 목적과 정확히 매치되는 문맥에서 가정 [H]를 찾도록
       시도한다.  만일 찾으면 [apply H]와 같이 동작한다.

     - [contradiction]: [False]와 논리적으로 동치인 현재 문맥에서 가정
       [H]를 찾으리려고 시도한다. 만일 그러한 가정을 찾으면 목적을
       증명한다.

     - [constructor]: 현재 목적을 증명하는데 적용할 수 있는 (현재
       환경에서 어떤 [Inductive] 정의로부터) 생성자 [c]를 찾도록 시도하자.
       만일 찾으면 [apply c]처럼 동작하시오.

    진행하면서 예제들을 살펴볼 것이다. *)

(* ################################################################# *)
(** * 관계로 계산을 정의하기 *)

(** [aeval]과 [beval]을 [Fixpoints]로 정의한 함수로 제시하였다.
    계산에 대해 생각하는 다른 방법은 식과 값 사이의 _관계_이다.  종종
    더 유연한 방법이라는 것을 알게 될 것이다. 이 방법은 산술식에 대한
    다음 정의와 같이 자연스럽게 [Inductive] 정의를 사용한다... *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum  : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(** [aevalR]을 중위 표기법으로 표현하는 것은 편리할 것이다.  [e \\
    n]이라 작성하여 산술식 [e]를 값 [n]으로 계산하는 것을 의미한다. *)

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

(** 사실, 콕은 [aevalR] 자체의 정의에서 이 표기법을 사용하는 방법을
    제공한다.  [e \\ n] 형태의 문장을 포함하는 증명에 관하여 작업하고
    있는 상황을 피해서 혼란을 줄이되, [aevalR e n]를 사용하여 작성한
    정의를 참조해야 한다.

    이 표기법을 먼저 "예약"하고 그 다음 표기법의 의미를 선언하여 정의한다. *)

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

(* ================================================================= *)
(** ** 추론 규칙 표기법 *)

(** 비형식적 논의에서 [aevalR]과 유사한 관계를 더 보기 좋은 _추론
    규칙_의 그래픽 형태로 규칙을 작성하는 것이 편리하다. 줄 위의
    가설에서 아래의 결론을 추론한다 ([IndProp] 장에서 추론 규칙들을
    이미 보았다).  *)

(** 예를 들어, 생성자 [E_APlus]는...

      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)

    ...추론 규칙으로 아래와 같이 작성할 것이다:

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 \\ n1+n2
*)

(** 형식적으로, 추론 규칙에 대해 깊이 설명할 내용이 없다. 추론 규칙은
    함축일뿐이다.  오른쪽에 규칙 이름을 생성자 이름으로 읽고 추론 규칙
    줄 위의 각 줄의 전제를 [->] 함축으로 읽을 수 있다. 규칙에 언급된
    모든 변수들 ([e1], [n1], 등)은 맨 앞에 전체 한정사에 묵시적으로
    한정된다. (그런 변수들을 _메타 변수_라고 부르고 우리가 정의하는
    언어의 변수와 구분한다. 당분간 산술식은 변수를 포함하지 않지만 곧
    더할 것이다.) 모든 규칙을 모아놓은 것을 [Inductive] 선언으로 감싼
    것으로 표현한다. 규칙 전체에 대한 설명은 비형식적으로 서술할 때
    생략하거나 "[aevalR]은 다음 규칙하에 닫힌 가장 작은 관계라 하자"와
    같이 말한다. *)

(** 예를 들어, [\\]는 이 규칙들로 닫힌 가장 작은 관계다.

                             -----------                               (E_ANum)
                             ANum n \\ n

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 \\ n1+n2

                               e1 \\ n1
                               e2 \\ n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 \\ n1-n2

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 \\ n1*n2
*)

(* ================================================================= *)
(** ** 정의들 간의 동치 *)

(** 계산을 관계로 정의한 것과 함수로 정의한 것이 일치하는 것을
    증명하는 것은 간단하다. *)

Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

(** 고차원 전술을 더 사용하면 꽤 조금 더 짧게 증명할 수 있다. *)

Theorem aeval_iff_aevalR' : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  (* 수업에서 다루었다 *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(** **** 연습문제: 별 세 개  (bevalR)  *)
(** [aevalR]과 동일한 스타일로 [bevalR] 관계를 작성하고 [beval]과
    동치임을 증명하시오. *)

Inductive bevalR: bexp -> bool -> Prop :=
(* 여기를 채우시오 *)
.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

End AExp.

(* ================================================================= *)
(** ** 계산 기반 vs. 관계 기반 정의 *)

(** 산술식과 부울식 계산을 정의할 때 함수 정의를 사용할 지 관계 정의를
    사용할 지 선택하는 것은 주로 취향 문제이다. 둘 다 동작한다.

    하지만 계산에 대한 함수 정의 보다 관계형 정의가 훨씬 좋은 상황이
    있다. *)

Module aevalR_division.

(** 예를 들어, 산술 연산을 확장해서 나눗셈 연산도 고려한다고 가정하자.*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.   (* <--- new *)

(** [aeval] 정의를 확장하여 이 새로운 연산을 처리하는 것은 간단하지
    않을 수 있다 ([ADiv (ANum 5) (ANum 0)]의 결과는 무엇이어야
    하는가?). 하지만 [aevalR]을 확장하는 것은 쉽다. *)

Reserved Notation "e '\\' n"
                  (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv :  forall (a1 a2: aexp) (n1 n2 n3: nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

(** 비결정적 숫자 생성 연산 [any]를 산술식에 추가하고 싶다고
    가정하자. 이 연산을 계산하면 임의의 숫자를 만들어낸다. (모든
    가능한 숫자들 중 _확률적_으로 선택하는 것과 동일하지 않음을
    주목하시오. 결과에 대한 어떤 특정 분포를 규정하지 않지만 어떤
    결과가 _가능한지_ 말하고 있을 뿐이다.) *)

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aexp : Type :=
  | AAny  : aexp                   (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

(** 다시 한 번 [aeval]을 확장하는 것은 약간 까다로울수 있다. 왜냐하면
    계산은 식에서 숫자로 가는 결정적 함수가 _아니기_ 때문이다. 하지만
    [aevalR]을 확장하는 것은 아무 문제가 없다. *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny \\ n                 (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(** 이 시점에서 의아해할 수 있다. 기본적으로 어떤 스타일을 사용해야
    하는가?  위 예제는 관계형 정의가 근본적으로 함수형 정의보다 더
    강력하다는 것을 보여준다. 함수로 표현하기 쉽지 않거나 정말로
    함수가 _아닌_ 이와 같은 상황을 위하여 선택할 여지가 없다.  하지만
    두 가지 스타일이 모두 가능한 경우는 어떠한가?

    관계형 정의를 선호하는 한 가지는 더 우아하고 이해학 쉽다고
    생각하기 때문이다.  다른 이유는 콕은 자동으로 [Inductive]
    정의로부터 좋은 인버전과 귀납적 원리를 생성하기 때문이다.

    반면에 함수형 정의가 종종 더 편리할 수 있다. 함수는 그 자체로
    결정적이고 모든 인자에 대해 정의되어 있다. 관계형 정의에서는 이
    성질들이 필요하면 명시적으로 증명해야 한다. 함수로 정의하면 콕의
    계산 방법을 이용하여 증명동안 식을 간단하게 만들 수도 있다.

    더우기 함수는 OCaml이나 Haskell로 실행가능한 코드를 직접 "추출"할
    수 있다.

    궁극적으로 이 선택은 특정 상황의 상세한 특징이나 단순히 취향에
    달려있곤 하다.  정말로 대규모 콕 개발에서 함수와 관계 스타일
    _둘다_ 정의하고 이 두 스타일이 일치함을 보이는 보조 정리를 두어
    양쪽 관점에서 스위치하면서 증명하는 상황을 흔하게 본다. *)

(* ################################################################# *)
(** * 변수를 포함하는 식 *)

(** 다시 Imp를 정의하는 문제로 돌아가보자. 다음에 할 일은 산술식과
    부울식에 변수를 추가하는 것이다. 간단하게 유지하기 위해서 모두
    전역 변수이고 변수에 숫자만 담을 수 있다고 가정할 것이다. *)

(* ================================================================= *)
(** ** 상태 *)

(** Imp 변수 타입에 대해 [Maps] 장에서 설명한 [id] 타입을 사용할
    것이다. 왜냐하면 변수를 들여다보고 현재 값을 찾아내야 하기
    때문이다.

    _기계 상태_ (또는 그냥 _상태_)는 프로그램 실행 중 어떤 지점에서
    _모든_ 변수의 현재 값을 표현한다. *)

(** 간단하게 하기 위해서, 주어진 프로그램은 유한한 수의 변수들을
    사용하지만 상태는 _모든_ 변수를 정의한다고 가정한다. 상태는
    메모리에 저장된 모든 정보를 담는다. Imp 프로그램의 각 변수에
    자연수를 저장하기 때문에 상태를 식별자에서 [nat]로의 매핑으로
    상태를 표현할 수 있다. 더 복잡한 프로그래밍언어의 경우 더 복잡한
    구조의 상태를 두어야 할 것이다. *)

Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.

(* ================================================================= *)
(** ** 구문  *)

(** 이전 산술식에 생성자를 하나 더 간단히 추가하여 변수를 추가할 수
있다. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

(** 두세 가지 변수 이름을 정의해서 축약된 표기법으로 사용한다. 나중에
    예제를 쉽게 읽을 수 있도록 한다. *)

Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".

(** 프로그램 변수 이름짓는 약속 ([X], [Y], [Z]은 타입을 대문자로
    사용하던 것과 조금 충돌난다. Imp에 관한 장들에서 다형성을 많이
    사용하지 않기 때문에 오버로딩으로 혼동스럽지 않을 것이다.) *)

(** [bexp]의 정의는 그대로 둔다 (새로운 [aexp]를 사용하는 것만
    제외하고).  *)

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(* ================================================================= *)
(** ** 계산 *)

(** 산술식과 부울식 계산기를 변수를 처리하도록 상태를 추가 인자로 받는
    명백한 방식으로 확장한다. *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (t_update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (t_update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * 명령어 *)

(** Imp _명령어_의 구문(_문장_이라고 부르기도 한다)과 동작을 정의할
    준비가 이제 되었다. *)

(* ================================================================= *)
(** ** 구문 *)

(** 비형식적으로 명령어 [c]는 다음 BNF 문법으로 기술한다. (콕 표기법 방법을 사용하여 
    Imp 구문을 정의할 수 있도록 다소 어색한 구체적인 구문을 선택한다. 특히 [IFB]를
    사용하여 표준 라이브러리 [if] 표기법과 충돌하지 않도록 피한다.)

     c ::= SKIP | x ::= a | c ;; c | IFB b THEN c ELSE c FI
         | WHILE b DO c END
*)
(**
    예를 들어, Imp로 작성한 팩토리얼 프로그램이다.

     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END

   이 명령어가 종료하면 변수 [Y]는 초기값 [X]의 팩토리얼을 포함할 것이다. *)

(** 다음은 명령어의 추상 구문의 형식적인 정의다. *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

(** 대개 그러하듯이 두세 가지 [Notation] 선언을 사용하여 가독성을 높일
    수 있다.  콕의 내장된 표기법과 충돌나지 않도록 가볍게 구문을
    유지한다. 특히 이미 저의한 숫자 연산자와 부울 연산자와 혼동을
    피하기 위해 [aexps]와 [bexps]에 대한 표기법은 도입하지 않는다.  *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** 예를 들어, 여기 다시 콕의 형식적인 정의로 표현한 팩토리얼 함수가
    있다. *)

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

(* ================================================================= *)
(** ** 더 많은 예제들 *)

(** 할당문: *)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

(* ----------------------------------------------------------------- *)
(** *** 반복문 *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

(* ----------------------------------------------------------------- *)
(** *** 무한 반복문 *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(* ################################################################# *)
(** * 명령어를 실행하기 *)

(** 다음으로 Imp 명령어를 실행하는 것이 의미하는 바를 정의할 필요가
    있다. [WHILE] 반복문은 반드시 종료하지 않아도 되기 때문에 실행
    함수를 정의할 때 까다롭다... *)

(* ================================================================= *)
(** ** 함수로 명령어 실행하기 (실패한 시도) *)

(** [WHILE] 경우를 생략하고 명령어를 실행하는 함수를 정의해본다.  *)

Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        t_update st x (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.

(** OCaml이나 Haskell과 같은 전통적인 함수형 프로그래밍 언어에서
    다음과 같이 [WHILE]을 추가할 수도 있을 것이다.

  Fixpoint ceval_fun (st : state) (c : com) : state := match c with
    ...  | WHILE b DO c END => if (beval st b) then ceval_fun st (c;
    WHILE b DO c END) else st end.

    콕은 이런 정의를 받아들이지 않는다 ("에러: fix의 감소하는 인자를
    추측할 수 없다"). 왜냐하면 정의하고자 하는 함수가 종료하지 않을 수
    있기 때문이다. 정말로 항상 종료하는 것은 _아니다_. 예를 들어
    [ceval_fun] 함수의 전체 버전을 위의 [loop] 프로그램에 적용하면
    결코 종료하지 않을 것이다. 콕은 단지 함수형 프로그래밍 언어일 뿐만
    아니라 일관성있는 논리이기 때문에 잠재적으로 종료하지 않는 함수는
    제외할 필요가 있다. 만일 콕에서 비종료 재귀함수를 허용하면 잘못될
    수 있다는 것을 보여주는 (무효!) 프로그램이 여기 있다.

         Fixpoint loop_false (n : nat) : False := loop_false n.

    즉 [False]와 같은 명제가 증명 가능할 수 있게 될 것이다
    ([loop_false 0]는 [False]를 증명하는 것이다). 이러한 상황으로 콕의
    논리적 일관성에 재앙이 발생할 것이다.

    이렇게 [ceval_fun]의 모든 입력에 대해 종료하지 않기 때문에 콕으로
    작성할 수 없다.  작성하려면 추가적인 트릭과 회피 방법이 필요하다
    (이러한 방법이 무엇인지 궁금하면 [ImpCEvalFun] 장을 보시오).  *)

(* ================================================================= *)
(** ** 관계로 계산하기 *)

(** 여기 더 나은 방법이 있다. [ceval]을 _함수_가 아닌 _관계_로
    정의하라. 즉, 앞에서 [aevalR]에 대해 그랬듯이 [Type] 대신
    [Prop]으로 정의하라. *)

(** 이 것은 중요한 변화다. 서투른 대체 방법을 사용하지 않고 정의에서
    더 많은 유연성을 준다. 예를 들어, [any] 같은 비결정적 특징을
    언어에 추가하려면 실행 정의도 비결정적이기를 원한다. 즉, 전사
    매핑도 아니고 함수도 아니다! *)

(** [ceval] 관계를 [c / st \\ st'] 표기법을 사용할 것이다.  [c / st \\
    st']는 시작 상태 [st]에서 프로그램 [c]를 실행하고 종료 상태
    [st']를 결과로 낸다. "[c]는 [st]를 받아서 [st']으로 간다"라고 읽을
    수 있다. *)

(* ----------------------------------------------------------------- *)
(** *** 실행과정을 고려한 의미 *)

(** 계산에 관한 비정형적 정의는 다음과 같다. 가독성을 위하여 추론 규칙으로 표현하였다. 


                           ----------------                            (E_Skip)
                           SKIP / st \\ st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   x := a1 / st \\ (t_update st x n)

                           c1 / st \\ st'
                          c2 / st' \\ st''
                         -------------------                            (E_Seq)
                         c1;;c2 / st \\ st''

                          beval st b1 = true
                           c1 / st \\ st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st \\ st'

                         beval st b1 = false
                           c2 / st \\ st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st \\ st'

                         beval st b = false
                    ------------------------------               (E_WhileFalse)
                    WHILE b DO c END / st \\ st

                          beval st b = true
                           c / st \\ st'
                  WHILE b DO c END / st' \\ st''
                  ---------------------------------               (E_WhileTrue)
                    WHILE b DO c END / st \\ st''
*)

(** 여기 형식적인 정의가 있다. 이 것이 어떻게 추론 규칙에 상응하는지
    확실히 이해하시오.  *)

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

(** 함수 대신 관계로 계산을 정의하면 어떤 프로그램이 어떤 결과 상태로
    계산되는 _증명_을 이제 만들 필요가 있다. 콕의 계산 방법을 그대로
    활용할 수는 없다. *)

Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   \\ (t_update (t_update empty_state X 2) Z 4).
Proof.
  (* 중간 상태를 제공해야 한다 *)
  apply E_Seq with (t_update empty_state X 2).
  - (* 할당 명령어 *)
    apply E_Ass. reflexivity.
  - (* 조건 명령어 *)
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(** **** 연습문제: 별 두 개 (ceval_example2)  *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state \\
    (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개, 고급 (pup_to_n)  *)
(** [1]부터 [X]까지 숫자들을 합하는 [1 + 2 + ... + X] Imp 프로그램을
    작성하시오. [X] = [2]에 대해서 이 프로그램이 의도한 대로
    실행한다고 증명하시오 (이 증명은 생각보다 더 까다롭다). *)

Definition pup_to_n : com
  (* 이 줄을 당신의 정의로 바꾸시오 *). Admitted.

Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) \\
    t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 실행 결정성 *)

(** 실행을 계산 기반 정의에서 관계형 정의로 바꾸는 것은 좋다. 왜냐하면
    실행이 전사 함수이어야 한다는 가공의 요구사항을 따를 필요가 없기
    때문이다. 하지만 의문이 발생한다. 실행의 두번째 정의는 정말로 부분 함수인가?
    아니면 동일한 상태 [st]에서 시작해서 명령어 [c]를 다른 방법으로 실행하여 
    두 가지 다른 출력 상태들 [st']과 [st'']에 도달할 수 있을까?

    사실 이런 상황은 발생할 수 없다. [ceval]은 부분 함수_이다_. *)

Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b1은 true로 계산된다 *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b1은 false로 계산된다 (모순) *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1은 true로 계산된다 (모순) *)
    rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1은 false로 계산된다 *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b1은 false로 계산된다 *)
    reflexivity.
  - (* E_WhileFalse, b1은 true로 계산된다 b1 evaluates to true (모순) *)
    rewrite H in H2. inversion H2.
  - (* E_WhileTrue, b1은 false로 계산된다 (모순) *)
    rewrite H in H4. inversion H4.
  - (* E_WhileTrue, b1은 true로 계산된다 *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * Imp 프로그램에 대한 추론 *)

(** 다음 장들에서 Imp 프로그램에 대해 추론하는 체계적인 기법들을 더
    자세하게 살펴볼 것이다. 하지만 정의 자체만으로 꽤 많은 것을 할 수
    있다.  이 절에서 몇 가지 예제들을 살핀다. *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st \\ st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

  (** [Heval]을 인버팅하여 [ceval] 계산의 한 단계를 확장한다.  이 경우
      [plus2]는 할당문이므로 [st']은 [X]의 새로운 값으로 확장한
      [st]이어야 한다. *)

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(** **** 연습문제: 별 세 개, 추천 (XtimesYinZ_spec)  *)
(** [XtimesYinZ]의 명세를 기술하고 증명하시오. *)

(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 세 개, 추천 (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.

  (** [loopdef]가 종료함을 보이는 가정한 유도에 대한 귀납법에 따라
      진행하시오.  대부분의 경우 즉시 모순이 발생한다 (그리고
      [inversion]으로 진행한 한 단계에서 해결될 수 있을 것이다.) *)

  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개 (no_whilesR)  *)
(** 다음 함수를 고려하자 *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.

(** 이 명제는 while 반복문이 없는 프로그램의 경우에 대해서만 [true]를
    낸다.  [Inductive]를 사용하여 [no_whilesR] 성질을
    작성하시오. [no_whilesR c]는 [c]에 while 반복문이 없는 프로그램일
    때 증명가능하다는 성질이다. 그런 다음 [no_whiles]와 동치임을
    증명하시오. *)

Inductive no_whilesR: com -> Prop :=
 (* 여기를 채우시오 *)
.

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 네 개 (no_whiles_terminating)  *)
(** while 반복문을 포함하지 않는 Imp 프로그램은 항상 종료한다.  이에
    관한 [no_whiles_terminating] 정리를 기술하고 증명하시오. *)
(** [no_whiles]이나 [no_whilesR] 중 선호하는 것을 사용하시오. *)

(* 여기를 채우시오 *)
(** [] *)

(* ################################################################# *)
(** * 추가 연습문제 *)

(** **** 연습문제: 별 세 개 (stack_compiler)  *)
(** HP 계산기, Forth와 Postscript 같은 프로그래밍 언어, Java
    가상기계와 같은 추상 기계는 모두 스택을 사용하여 산술식을
    계산한다. 예를 들어, 식

      (2*3)+(3*(4-2))

   은 다음과 같은 순서로 입력하고

      2 3 * 3 4 2 - * +

   그리고 이렇게 계산한다 (오른편에 실행 과정의 프로그램과 왼편에 스택
   내용을 보여준다).

      [ ] | 2 3 * 3 4 2 - * + [2] | 3 * 3 4 2 - * + [3, 2] | * 3 4 2 -
      * + [6] | 3 4 2 - * + [3, 6] | 4 2 - * + [4, 3, 6] | 2 - * + [2,
      4, 3, 6] | - * + [2, 3, 6] | * + [6, 6] | + [12] |

  이 연습문제에서 할 일은 [aexp]를 스택 기계 명령어로 번역하는 작은
  컴파일러를 작성하는 것이다.

  스택 언어에 대한 명령어 집합은 다음 명령어들로 구성될 것이다. [SPush
  n]: 숫자 [n]을 스택에 올려 넣는다. [SLoad x]: 변수 [x]의 값을
  메모리에서 불러와서 스택에 올려 넣는다. [SPlus]: 스택 맨 위 두
  숫자들을 꺼내서 더하고 그 결과를 다시 스택에 올려 넣는다. [SMinus]:
  비슷한 방식으로 뺄셈을 수행한다. [SMult]: 비슷한 방식으로 곱셈을
  한다. *)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(** 스택 언어에서 프로그램을 계산하는 함수를 작성하시오. 입력으로
    상태, 숫자 리스트로 표현한 스택, 명령어 리스트로 표현한 프로그램을
    받아 프로그램 실행 후의 스택을 리턴해야 한다. 당신의 함수를 아래에
    나열된 예제들을 가지고 테스트하시오.

    [SPlus], [SMinus], [SMult] 명령어를 실행할 때 스택에 두 개 보다
    적은 원소를 포함한다면 어떻게 해야할지 명령어 명세에 규정되어 있지
    않음을 주목하라. 어떤 면에서는 그러한 상황에 무엇을 할 지 중요하지
    않다. 왜냐하면 우리 컴파일러는 그러한 잘못 구성된 프로그램을 결코
    만들지 않을 것이기 때문이다. *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat
  (* 이 줄을 당신의 정의로 바꾸시오 *). Admitted.

Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
(* 여기를 채우시오 *) Admitted.

Example s_execute2 :
     s_execute (t_update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
(* 여기를 채우시오 *) Admitted.

(** 다음으로 [aexp]를 스택 기계 프로그램으로 컴파일하는 함수를
    작성하시오.  프로그램을 실행하는 효과는 그 식의 값을 스택에 올려
    놓는 것과 동일해야 한다.  *)

Fixpoint s_compile (e : aexp) : list sinstr
  (* 이 줄을 당신의 정의로 바꾸시오 *). Admitted.

(** [s_compile]을 정의한 다음 동작 여부를 테스트하기 위해 다음을
    증명하시오. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
(* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 네 개, 고급 (stack_compiler_correct)  *)
(** 이전 연습문제에서 구현한 컴파일러의 정확성을 이제 증명할 것이다.
    [SPlus], [SMinus], [SMult] 명령어가 두 개 보다 적은 원소들을
    포함하는 스택을 만나면 무엇을 할 지 명세에서 규정하고 있지 않음을
    기억하시오 (정확성 증명을 더 쉽게 하려면 돌아가서 구현 방법을
    변경하는 것이 필요할 수도 있다!).

    다음 정리를 증명하시오. 더 일반적인 보조 정리를 기술하여 사용할 수
    있는 귀납적 가정을 얻을 필요가 있을 것이다. 주 정리는 이 보조
    정리의 간단한 따름 정리가 될 것이다. *)


Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개, 선택 사항 (short_circuit)  *)
(** 대부분의 현대 프로그래밍 언어는 부울 [and]에 대한 "단락" 계산
    규칙을 사용한다.  [BAnd b1 b2]를 계산하려면 먼저 [b1]을
    계산한다. 그 결과가 [false]이면 [b2]를 계산하지 않고 전체 [BAnd]
    식이 즉시 [false]가 된다. 그렇지 않다면 [b1]를 계산해서 [BAnd]
    식의 결과를 결정한다.

    설명한 방식으로 [BAnd]의 단락 계산을 수행하도록 [beval]의 대체
    버전을 작성하고, [beval]과 동치임을 증명하시오. *)

(* 여기를 채우시오 *)
(** [] *)

Module BreakImp.
(** **** 연습문제: 별 네 개, 고급 (break_imp)  *)

(** C와 Java 같은 명령형 언어는 반복문 실행을 중지하는 [break]나
    비슷한 문장을 포함한다. 이 연습문제에서 Imp에 [break]를 추가하는
    법을 고려하자. 우선 명령어 언어를 추가 명령어로 확장할 필요가
    있다. *)

Inductive com : Type :=
  | CSkip : com
  | CBreak : com               (* <-- new *)
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** 그 다음 [BREAK]의 동작을 정의할 필요가 있다. 비형식적으로 일련의
    명령어들 중 하나로 [BREAK]를 실행할 때 그 명령어들 실행을 중단하고
    가장 안쪽 내포된 반복문이 끝나야 한다고 알린다. (만일 감싸는
    반복문이 없으면 전체 프로그램이 종료한다.) 마지막 상태는 [BREAK]
    문장이 실행되었을 때 상태와 동일해야 한다.

    한 가지 중요한 점은 주어진 [BREAK]를 감싸는 여러 반복문들이 있을
    때 어떻게 동작할 지 정의하는 것이다. 그러한 경우에 [BREAK]는 _가장
    안쪽_ 반복문만 종료시킨다. 이렇게 다음을 실행한 다음...

       X ::= 0;; Y ::= 1;; WHILE 0 <> Y DO WHILE TRUE DO BREAK END;; X
       ::= 1;; Y ::= Y - 1 END

    ... [X]의 값은 [1]이 되어야 하고 [0]이 아니다.


    이러한 동작을 표현하는 한 가지 방법은, 계산 관계에 새로운
    패러미터를 추가해서 다음 실행할 명령어가 [BREAK] 문장인지 규정하는
    것이다. *)

Inductive result : Type :=
  | SContinue : result
  | SBreak : result.

Reserved Notation "c1 '/' st '\\' s '/' st'"
                  (at level 40, st, s at level 39).

(** 직관적으로 [c / st \\ s / st']는 만일 [c]를 상태 [st]에서 시작하면
    [st']에서 종료하고 맨 안쪽에 감싸는 반복문 (또는 전체 프로그램)은
    즉시 빠져나가야 한다 ([s = SBreak]) 또는 이 실행은 정상적으로
    이어가야 한다 ([S = SContinue]).

    [c / st \\ s / st'] 관계의 정의는 정규 계산 관계 [c / st \\ st']를
    정의한 것과 매우 유사하다. 단지 종료할지 알리는 신호를 적절히
    처리할 필요만 있을 뿐이다.

    - [SKIP] 명령어의 경우 상태는 바뀌지 않고 감싸고 있는 어떤
      반복문도 정상적으로 실행을 계속한다.

    - [BREAK] 명령어의 경우 상태는 바뀌지 않지만 [SBreak] 신호를
      보낸다.

    - 할당문의 경우 현재 상태의 변수 값을 문장에 따라 바꾸고
      정상적으로 실행을 계속한다.

    - [IFB b THEN c1 ELSE c2 FI] 형태의 명령어의 경우 상태는 Imp의
      원래 의미에 따라 변경되도록 하되 어느 분기가 선택되었는지
      무관하게 그 분기를 실행하면서 발생한 신호를 전파한다.

    - [c1 ;; c2] 형태의 명령어의 경우 [c1]을 먼저 실행한다. 만일
      [SBreak] 신호가 발생하면 [c2]를 실행하지 않고 [SBreak] 신호를
      감싸는 문맥에 전파한다. 결과 상태는 [c1]을 실행하면서 얻는
      상태와 동일하다. 만일 [c1] 실행에서 [SBreak] 신호가 발생하지
      않으면 [c1]을 실행해서 얻은 상태에서 [c2]를 실행하고 거기에서
      발생한 신호가 있다면 전파한다.

    - 마지막으로 [WHILE b DO c END] 형태의 반복문의 의미는 이전과 거의
      동일하다.  유일하게 다른 점은 [b]가 true일 때 [c]를 계산하고
      [c]에서 신호를 발생했는지 검사하는 것이다. 신호가
      [SContinue]이면 원래 의미대로 실행을 진행하간다.  그렇지 않으면
      반복문 실행을 멈추고 결과 상태를 현재 반복의 실행에서 나온
      상태와 동일하다. 어느 경우든 [BREAK]는 가장 안쪽의 반복문만을
      종료시키기 때문에 [WHILE]은 [SContinue] 신호를 낸다.  *)

(** 위에서 기술한 바에 따라 [ceval] 관계를 정의하시오. *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      CSkip / st \\ SContinue / st
  (* 여기를 채우시오 *)

  where "c1 '/' st '\\' s '/' st'" := (ceval c1 st s st').

(** 이제 [ceval] 정의 다음 성질들을 증명하시오.  *)

Theorem break_ignore : forall c st st' s,
     (BREAK;; c) / st \\ s / st' ->
     st = st'.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st \\ s / st' ->
  s = SContinue.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st \\ SBreak / st' ->
  (WHILE b DO c END) / st \\ SContinue / st'.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개, 고급, 선택 사항 (while_break_true)  *)
Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st \\ SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' \\ SBreak / st'.
Proof.
(* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 네 개, 고급, 선택 사항 (ceval_deterministic)  *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st \\ s1 / st1  ->
     c / st \\ s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* 여기를 채우시오 *) Admitted.

(** [] *)
End BreakImp.

(** **** 연습문제: 별 네 개, 선택 사항 (add_for_loop)  *)
(** C 스타일 [for] 반복문을 명령어 언어에 추가하고, [for] 반복문의
    의미를 정의하도록 [ceval] 정의를 수정하고, [for] 반복문에 필요한
    경우들을 추가해서 이 파일에 있는 모든 증명을 여전히 콕이
    받아드리도록 작성하시오.

    [for] 반복문은 (a) 처음 실행하는 문장, (b) 반복문의 각 반복마다 이
    반복문을 계속 수행할지 결정하기 위해서 실행하는 검사, (c) 반복문의
    각 반복의 끝에 실행할 문장, (d) 반복문의 몸체를 구성하는 문장으로
    구성되어 있다. ([for] 반복문의 실제 표기법을 구성하는 것에 대해서
    고민할 필요는 없다. 원한다면 이 표기법도 자유롭게 정의해보라.) *)

(* 여기를 채우시오 *)
(** [] *)

(** $Date: 2017-08-25 14:01:35 -0400 (Fri, 25 Aug 2017) $ *)

