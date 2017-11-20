(** * 논리: 콕에서 다루는 논리 *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.

(** 이전 장들에서 사실에 기반을 둔 주장(_명제_)의 많은 예들과 그것들이
    사실이라는 주장을 펴는 방법들(_증명_)을 보았다. 특히 [e1 = e2]
    형태의 _등식에 관한 명제_, 함축([P -> Q]), 한정사를 사용한
    명제([forall x, P])를 광범위하게 다루었다. 이 장에서 다른 익숙한
    형태들의 논리 추론을 하기 위해 어떻게 콕을 사용할 수 있는지를 보게
    될 것이다.

    상세한 내용을 살펴보기 전에, 콕으로 작성하는 수학적 문장의 상태에
    대해 조금 이야기하자. 콕은 _타입을 매기는_ 언어인데, 이는 콕의
    세계에 있는 모든 의미 있는 식은 연관된 타입을 갖는다는 것을 뜻한다.
    논리적 주장도 예외가 아니다. 왜냐하면 콕으로 증명하고자 시도하는
    어떤 문장도 타입을 가지고 있기 때문이다. _명제_의 타입인
    [Prop]이다. [Check] 명령어로 이것을 볼 수 있다.
*)

Check 3 = 3.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(** _모든_ 구문 규칙을 준수하는 명제들은 콕에서 [Prop] 타입을 갖는
    것에 주목하자.  이 명제들이 참이든 거짓이든 상관없이 이 타입을
    갖는다. *)

(** 단순히 명제의 _자격을 갖추는 것_과 명제가 참임을 _증명할 수 있는 것_은 
    별개의 문제다! *)

Check 2 = 2.
(* ===> Prop *)

Check forall n : nat, n = 2.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

(** 정말로 명제는 단지 타입만 가지고 있는 것이 아니다. 콕의 세계의 다른 것들처럼
    똑같은 방식으로 다룰 수 있는 _일 등급 객체_이다. 
 *)

(** 지금까지 명제를 작성할 수 있는 한 가지 주된 위치 [Theorem] (
    [Lemma]와 [Example]) 선언들만 보아왔다.  *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** 하지만 명제는 다른 많은 방법으로 사용할 수 있다. 예를 들어,
    [Definition]을 사용하여 명제에 다른 이름을 줄 수 있다. 마치 다른
    종류의 식에 이름을 붙이는 것처럼 말이다.  *)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** 나중에 명제를 기대하는 어떤 상황에서 이 이름을 사용할 수
    있다. 예를 들어, [Theorem] 선언의 주장으로 사용할 수 있다. *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** _매개 변수를 갖는_ 명제도 작성할 수 있다. 즉, 어떤 타입의 인자들을
    받아 명제를 리턴하는 함수들을 작성할 수 있다. *)

(** 예를 들어, 다음 함수는 숫자를 받아 이 숫자가 3과 같다고 주장하는
    명제를 리턴한다. *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(** 콕에서 명제를 리턴하는 함수는 그 함수 인자의 _성질_을 정의한다라고 한다.

    예를 들어, _단사 함수_라는 익숙한 개념을 다음과 같이 정의한다.
 *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

(** 동치 연산자 [=]는 [Prop]을 리턴하는 함수이기도 하다.

    식 [n = m]은 [eq n m]을 보기 좋게 표현한 것인데, 콕의 [Notation]
    방법을 사용하여 정의한 것이다. [eq]은 어떠한 타입의 원소들과 함께 사용할 수 있기
    때문에 이 함수도 다형성을 갖는다. *)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(** ([eq] 대신 [@eq]라고 작성했음을 주목하시오. [eq]에 대한 타입 인자
    [A]는 묵시적으로 선언되어서 [eq]의 전체 타입을 보려면 묵시적 인자
    기능을 중지시킬 필요가 있다.) *)

(* ################################################################# *)
(** * 논리적 연결자 *)

(* ================================================================= *)
(** ** 논리곱 *)

(** 명제 [A]와 [B]의 _논리곱_은 [A /\ B]라고 작성하고, [A]와 [B]가
    둘 다 참이라는 주장을 표현한다. 
 *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** 논리곱을 증명하기 위해 [split] 전술을 사용한다. 이 전술로 이 문장의 각 부분에 대해
    하나씩 두 개의 부분 목적들을 설정할 것이다. *)

Proof.
  (* 수업에서 다루었음 *)
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** 어떤 명제 [A]와 [B]에 대해 [A]가 참이라고 가정하고 [B]가 참이라고
    가정하면 [A /\ B]도 참이라고 결론 지을 수 있다.  *)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(** 가정들과 함께 정리를 어떤 목적에 적용하면 이 정리를 위해 필요한
    가정들의 수만큼의 부분 목적들을 새로 만들어내는 효과가 있기
    때문에 [and_intro]를 적용해서 [split]와 동일한 효과를 얻을 수
    있다.
     *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** 연습문제: 별 두 개 (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** 논리곱 문장을 증명하는 것에 대해서는 이쯤 해두자. 나머지 다른
    방향에 대해서 즉, 그 밖에 무엇인가를 증명하기 위해 논리곱 가정을
    _사용_하려면 [destruct] 전술을 사용한다.

    증명 문맥에 [A /\ B] 형태의 가정 [H]를 포함하는 경우 [destruct H
    as [HA HB]]라고 명령을 내리면 [H]를 이 문맥에서 없애고 두 개의
    새로운 가정들: [A]가 참이라는 [HA]와 [B]가 참이라는 [HB]을 새로
    추가한다.
  *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* 수업에서 다루었음 *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** 대개 그러하듯이 [H]를 도입한 다음 분해하지 않고 도입하자마자
    분해도 할 수 있다.
 *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** 두 가정들 [n = 0]과 [m = 0]을 하나의 논리곱으로 묶는 것을 왜
    꺼려했는지 궁금할 수도 있다. 왜냐하면 두 개의 분리된 전제들을
    가지고 이 정리를 작성할 수 있었기 때문입니다.
 *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** 이 정리를 작성하기 위해서라면 두 가지 작성 방법 모두
    좋습니다. 하지만 논리곱 가정들을 어떻게 다루는지 이해하는 것이
    중요합니다. 왜냐하면 논리곱은 증명 중간 단계에 빈번하게 발생할 수
    있기 때문입니다. 특히 매우 큰 증명 과정 중에. 여기 간단한 예가
    있습니다.
 *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** 논리곱에 대한 다른 흔하게 발생하는 상황은 [A /\ B]가 참이지만 어떤
    경우에는 단지 [A]만 (또는 [B]만) 필요한 상황이다. 다음 보조
    정리들은 그러한 경우에 유용하다.
 *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.  Qed.

(** **** 연습문제: 별 한 개, 선택 사항 (proj2)  *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** 마지막으로 논리곱의 순서나 여러 피연산자들을 갖는 논리곱의 그룹을
    재배치할 필요가 있다.  다음 교환 법칙과 결합 법칙 정리들은 그런
    경우에 편리하다.
 *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* 수업에서 다루었음 *)
  intros P Q [HP HQ].
  split.
    - (* 왼쪽 *) apply HQ.
    - (* 오른쪽 *) apply HP.  Qed.
  
(** **** 연습문제: 별 두 개 (and_assoc)  *)
(** (결합성에 대한 다음 증명에서 _내포된_ intro 패턴이 가정 [H : P /\
    (Q /\ R)]을 [HP : P], [HQ : Q], [HR : R]로 분해하는 과정을
    주목하시오. 거기에서부터 증명을 완료하시오.) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** 그런데 중위 연산자 [/\]는 사실 [and A B]를 구문상으로 직관적으로
    보이도록 만든 표기법일 뿐이다. 즉, [and]는 두 개의 명제들을 인자로
    받아 하나의 명제를 내는 콕 연산자이다.
 *)

Check and.
(* ===> and : Prop -> Prop -> Prop *)

(* ================================================================= *)
(** ** 논리합 *)

(** 다른 중요한 논리 연결자는 두 명제의 _논리합_이다. [A] 또는 [B]가
    참이면 [A \/ B]가 참이다. ([or : Prop -> Prop -> Prop]를 사용하여
    [or A B]로 논리합을 작성할 수 있다.) *)

(** 증명에서 논리합 가정을 사용하려면 [nat]이나 다른 데이터 타입에
    대해 진행한 것과 같이 경우 별 분석으로 진행한다. 경우 별 분석은
    [destruct]나 [intros]를 가지고 진행할 수 있다.  여기 예가 있다. *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* 이 패턴은 [n = 0 \/ m = 0]에 대해 묵시적으로 경우 별로 분석한다. *)
  intros n m [Hn | Hm].
  - (* 이 경우는 [n = 0] *)
    rewrite Hn. reflexivity.
  - (* 이 경우는 [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** 역으로 논리합이 성립하는 것을 보이려면 둘 중 하나만 성립하는 것을
    보이면 된다.  이때 [left]와 [right] 두 가지 전술을
    사용한다. 전술의 이름에서 알 수 있듯이 첫 번째 전술은 논리합의
    왼편을 증명하면 되고, 두 번째 전술은 오른편을 증명한다.  여기 매우
    단순한 사용 예가 있다... *)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** ... 그리고 [left]와 [right]를 둘 다 사용해야 하는 조금 더 흥미로운
    예가 있다.  *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** **** 연습문제: 별 한 개 (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 한 개 (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 거짓과 부정 *)

(** 이제까지 주로 어떤 것이 _참_이라는 것을 증명하는 것에
    관여해왔다. 덧셈의 교환 법칙이 성립하고, 두 리스트를 붙이는 연산은
    결합 법칙이 성립하며, 등등. 물론 어떤 명제들이 참이 _아니다_라는
    _부정적인_ 결과에도 관심이 있을 수 있다. 그러한 부정적인 문장들을
    콕에서는 부정 연산자 [~]로 표현한다. *)

(** 부정이 어떻게 동작하는지 보기 위해서 [Tactics] 장에서 _부정의 함축
    원리(principle of explosion)_에 관해 논의한 것을 기억하자.  이
    원리가 얘기하는 바는, 만일 우리가 모순을 가정하면 어떤 명제도
    유도할 수 있다는 것이다. 이 직관을 따르면 [~ P] ("not [P]")를
    [forall Q, P -> Q]로 정의할 수 있을 것이다. 콕에서는 사실 [~ P]를
    [P -> False]로 약간 다르게 정의한다. 이때 [False]는 표준
    라이브러리에서 정의한 모순된 명제이다.
 *)

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

(** [False]는 모순된 명제이기 때문에 부정의 함축 원리를 이것에도
    적용한다.  만일 [False]를 증명 문맥에 추가한다면 [destruct] (또는
    [inversion]) 전술을 이 모순 명제에 적용하여 어떠한 목적도 달성할
    수 있다.
 *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* 수업에서 다루었음 *)
  intros P contra.
  destruct contra.  Qed.

(** 라틴어 _ex falso quodlibet_는 문자 그대로 "네가 바라는 것
    무엇이든지 거짓으로부터 끌어낼 수 있다"를 의미한다. 이 것은 부정의
    함축 원리에 대한 또 다른 흔한 이름이다.
 *)

(** **** 연습문제: 별 두 개, 선택 사항 (not_implies_our_not)  *)
(** 부정에 대한 콕의 정의로부터 바로 위에서 언급한 직관적인 명제를
    유도할 수 있음을 보이시오. *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** 다음은 [0]과 [1]은 [nat]의 다른 원소들이라는 것을 서술하기 위해
    [not]을 사용하는 방법이다.
 *)

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

(** 이러한 등식에 대한 부정 형태의 문장은 충분히 자주 나타나므로
    특별한 표기법 [x <> y]을 도입할 필요가 있다.  *)

Check (0 <> 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.

(** 콕에서 부정을 가지고 작업하는 것에 익숙해지기 위해서 약간 연습이
    필요하다.  비록 부정을 포함하는 문장이 왜 참인지 완벽하게 잘
    이해할 수 있지만 콕이 그것을 이해할 수 있도록 적절한 설정을 만드는
    것은 처음에 약간 복잡할 수 있다.  여기 몇 가지 익숙한 사실들을
    증명해봄으로써 조금씩 익숙해지도록 하자.
*)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* 수업에서 다루었음 *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* 수업에서 다루었음 *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** 연습문제: 별 두 개, 고급, 추천 (double_neg_inf)  *)
(**  [double_neg]의 비형식적인 증명을 작성해보시오:

   _Theorem_: [P] implies [~~P], for any proposition [P]. *)

(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 두 개, 추천 (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 한 개 (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 한 개, 고급 (informal_not_PNP)  *)
(** 명제 [forall P : Prop, ~(P /\ ~P)]를 영어로 비형식적인 증명을
    작성하시오. *)

(* 여기를 채우시오 *)
(** [] *)

(** 비슷하게 부등식은 부정을 사용하기 때문에 부등식을 가지고 능숙하게
    증명할 수 있으려면 약간 연습을 요구한다. 여기 유용한 요령이 있다.
    성립하지 않는 목적 (예를 들어 [false = true]와 같은 목적)을
    증명하려 한다면 [ex_falso_quodlibet]을 적용해서 이 목적을
    [False]로 변경하라. 어쩌면 문맥에 있는 [~P] 형태의 가정을 사용하기
    더 쉬울 것이다. 특히 [x<>y] 형태의 가정도 사용하기 더 쉬울 것이다.
    *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** [ex_falso_quodlibet]로 추론하는 것이 상당히 흔해서 콕에서 미리
    준비된 전술 [exfalso]을 제공하므로 이 것을 적용하자.  *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.

(* ================================================================= *)
(** ** 참 *)

(** [False] 이외에도 콕은 표준 라이브러리에 [True]도 정의한다. 말
    그대로 참인 명제이다.  이 것을 증명하려면 미리 정의된 상수 [I :
    True]를 사용한다.  *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** [False]는 널리 사용되는 반면에 [True]는 매우 드물게
    사용된다. 왜냐하면 목적으로 증명하는 것이 매우 사소해서 그다지
    흥미롭지 않기 때문이다. 그리고 가정으로 유용한 정보를 제공하지
    않는다. 하지만 조건부 또는 고차원 [Prop]에 대한 매개변수로서
    복잡한 [Prop]를 정의할 때 상당히 유용할 수 있다. [True]를 그러한
    용도로 사용하는 예제들을 나중에 보게 될 것이다.
  *)

(* ================================================================= *)
(** ** 논리적 동치 *)

(** 편리한 "if and only if" 연결자는 두 명제가 동일한 진리 값을
    갖는다고 서술한다.  이 것은 함축 연결자 두 개를 논리곱으로 표현한
    것에 해당한다.  *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* 수업에서 다루었음 *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* 수업에서 다루었음 *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. inversion H'.
Qed.

(** **** 연습문제: 별 한 개, 선택 사항 (iff_properties)  *)
(** [<->]이 대칭 [iff_sym] 임을 보이는 위의 증명을 가이드로 사용하여
    이 연결자가 반사적이고 추이적인 성질도 가지고 있음을
    증명하시오. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개 (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** 어떤 콕 전술을 사용하면 [iff] 문장을 특별하게 취급해서 증명 상태를
    상세하게 다루지 않아도 됩니다. 특히 [rewrite]와 [reflexivity]
    전술은 단지 등식뿐만 아니라 [iff] 문장을 가지고 사용할 수 있다.
    이 동작을 사용하려면 등식뿐만 아니라 다른 공식들을 가지고 다시
    작성하도록 하는 특별한 콕 라이브러리를 불러들일 필요가 있다. *)

Require Import Coq.Setoids.Setoid.

(** 이 전술들이 [iff]를 어떻게 다루는지 보여주는 간단한 예가 있다.
    우선 기본적인 iff 동치 한 두 가지를 증명해보자... *)

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** [rewrite]와 [reflexivity] 전술들을 가지고 이 사실들을 이제
    사용하여 동치 형태의 문장을 매끄럽게 증명할 수 있다. 다음은 이전에
    증명한 바 있는 [mult_0] 결과에서 3개의 피연산자를 포함하는
    버전이다. *)

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

(** [apply] 전술도 [<->]과 함께 사용할 수 있다. 인자로 동치 형태가
    주어지면 [apply]는 그 동치의 어떤 편을 사용할지 추측한다. *)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* ================================================================= *)
(** ** 존재 한정 *)

(** 다른 중요한 논리 연결자는 _존재 한정_이다. 타입 [T]의 어떤 [x]가
    존재하여 [x]에 대한 어떤 성질 [P]가 성립한다는 것을 [exists x : T,
    P]라고 작성하여 표현한다.  만일 콕이 현재 문맥으로부터 [x]의
    타입을 유추할 수 있다면 [forall]의 경우처럼 [: T] 타입 주석을
    생략할 수 있다. *)

(** [exists x, P] 형태의 문장을 증명하려면 [x]를 위해 특별히 선택한
    값에 대해 [P]가 성립함을 보여야 한다. 이 증명은 두 단계로
    이루어진다. 첫째, [exists t] 전술로 우리가 아는 목격자 [t]를
    콕에게 명시적으로 알려준다. 그런 다음 [x]가 나타난 자리를 모두
    [x]로 바꾼 다음 [P]가 성립함을 증명한다. *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

(** 역으로 만일 존재 한정 [exists x, P] 명제를 현재 문맥에서 가지고
    있다면 이 것을 분해해서 어떤 목격자 [x]와 [x]에 대해 [P]가
    성립한다는 가정을 얻어 낼 수 있다. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* 수업에서 다루었음 *)
  intros n [m Hm]. (* 여기 묵시적으로 [destruct]를 적용함을 주목하시오 *)
  exists (2 + m).
  apply Hm.  Qed.

(** **** 연습문제: 별 한 개 (dist_not_exists)  *)
(** 모든 [x]에 대해 [P]가 성립하면 [P]가 성립하지 않는 [x]가 없음을
    증명하시오. *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 두 개 (dist_exists_or)  *)
(** 논리합에 대한 존재 한정 분배를 증명하시오. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 명제를 다루는 프로그래밍 *)

(** 이제까지 살펴본 논리 연결자들은 간단한 명제에서부터 복잡한 것들을
    정의하는데 풍성한 어휘를 제공한다. 예를 들어 원소 [x]가 리스트
    [l]에 나타난다는 주장을 표현하는 법을 살펴보자. 이 성질은 간단한
    재귀적 구조를 가지고 있음을 주목하시오.  *)
(**    - 만일 [l]이 비어있는 리스트이면 [x]는 그 리스트에 나타날 
         수 없다. 그래서 [x]는 [l]에 나타난다는 성질은 간단히 
         거짓이다. *)
(**    - 그렇지 않다면 [l]은 [x' :: l'] 형태이다. 이 경우 [x]가 
         [x']가 일치하거나 [l']에 나타나면 [x]가 [l]에 나타난다. *)

(** 이 성질을 원소와 리스트를 받아 명제를 리턴하는 간단한 재귀 함수로
    바로 변환할 수 있다. *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** [In]을 구체적인 리스트에 적용하면 내포된 논리합들이 쭉 나열된
    형태로 펼쳐진다. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* 수업에서 다루었음 *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* 수업에서 다루었음 *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.
(** (_덧붙여서_ 마지막 경우를 이행하기 위해서 비어있는 패턴을 사용함을
    주목하시오.) *)

(** [In]에 대한 더 일반적 형태이고 고차원인 보조 정리들도 증명할 수
    있다.

    다음 보조 정리 증명에서 [In]을 변수에 적용하여 시작하고 그 변수에
    대한 경우 별 분석을 하는 경우만 펼쳐지는 것을 주목하시오. *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, 모순 *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** 이렇게 재귀적으로 명제를 정의하는 방법은 어떤 경우에는 편리하지만
    약간의 단점도 있다. 특히 콕에서 재귀 함수를 정의할 때 반드시
    종료해야하는 조건에 관한 제약에 관한 것이다. 다음 장에서 명제들을
    _귀납적으로_ 정의하는 법을 살펴볼 것이다. 이 방법은 나름의 장점과
    한계를 갖는 다른 기법이다. *)

(** **** 연습문제: 별 두 개 (In_map_iff)  *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 두 개 (in_app_iff)  *)
Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개, 추천 (All)  *)
(** 명제를 리턴하는 함수를 그 함수 인자들의 _성질_로 볼 수 있다고 한
    점을 다시 기억하시오. 예를 들어 [P]가 [nat -> Prop] 타입을
    갖는다면 [P n]은 [n]에 대해 성질 [P]가 성립함을 서술한다.

    [In]으로부터 영감을 받아 리스트 [l]의 모든 원소들에 대해 성립하는
    어떤 성질 [P]를 기술하는 재귀 함수 [All]을 작성하시오. 당신이
    작성한 정의가 정확함을 확신하기 위해 [All_In] 보조 정리를 아래에서
    증명하시오. (물론 단순히 [All_In]의 왼편을 기술하지는 않도록
    한다.) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  (* 이 줄을 ":= _여러분의 정의_"로 다시 작성하시오 *). Admitted.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개 (combine_odd_even)  *)
(** 아래 [combine_odd_even] 함수의 정의를 완성하시오.  인자로 숫자들의
    두 가지 성질들, [Podd]와 [Peven]을 받아 [n]이 홀수 일 때 [P n]이
    [Podd n]과 동치이고 [n]이 짝수 일 때 [P n]이 [Peven n]과 동치인
    성질 [P]를 리턴해야 한다. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  (* 이 줄을 ":= _여러분의 정의_"로 다시 작성하시오 *). Admitted.

(** 작성한 정의를 테스트하기 위해 다음 사실들을 증명하시오. *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 정리를 인자에 적용하기 *)

(** 콕이 많은 다른 증명 보조기와 구분되는 한 가지 특징은 _증명_을 일
    등급 객체로 다룬다는 것이다.

    이것에 대해 이야기할 것이 많이 있지만 콕을 사용하기 위해서 이것을
    상세히 이해할 필요는 없다. 이 절은 단지 맛보기만 제공하고 더 깊은
    탐구는 선택 사항으로 분류된 장 [ProofObjects]와
    [IndPrinciples]에서 다룬다. *)

(** [Check] 명령어를 사용하여 콕으로 하여금 식의 타입을 출력하도록
    요청하는 것을 보아왔다. [Check] 명령어를 사용하여 특정 식별자가
    가리키는 정리가 무엇인지 콕에게 물어볼 수도 있다. *)

Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

(** 콕은 [Check]으로 어떤 식의 _타입_을 출력하는 것과 동일한 방법으로
    [plus_comm] 정리의 _문장_을 출력한다. 왜 그럴까? *)

(** 그 이유는 [plus_comm] 식별자는 사실 _증명 객체_를 가리키고 있기
    때문이다.  증명 객체는 [forall n m: nat, n + m = m + n] 문장이
    참임을 증명하는 논리적 유도과정을 표현하는 자료 구조이다. 이
    객체의 타입이 _바로_ 이 객체가 증명하는 정리의 문장이다.  *)

(** 직관적으로 정리의 문장은 그 정리를 사용할 목적이기 때문에 정리
    식별자를 [Check]로 확인하면 그 문장이 타입으로 출력되는 것이
    일리가 있다. 이것은 마치 계산을 담고 있는 객체의 타입이 그 객체를
    가지고 우리가 할 수 있는 것을 말해주는 것과 비슷하다. 예를 들어,
    [nat -> nat -> nat] 타입의 식을 가지고 있다면 그 식에 두 개의
    [nat]들을 인자로 주어 다시 [nat]을 돌려받을 수 있다. 비슷하게 [n =
    m -> n + n = m + m] 타입의 객체를 가지고 있고 타입 [n = m]의 어떤
    "인자"를 주면 [n + n = m + m]을 유도할 수 있다. *)

(** 그 과정을 생각하면 이러한 유사점은 한 걸음 더 나아갈 수
    있다. 정리를 마치 함수인 것처럼 타입이 매칭 되는 가정에 적용하여
    중간 단계의 주장들을 거치지 않고 정리의 결과를 그 가정에 맞추어
    특화시킬 수 있다. 예를 들어 다음 결과를 증명하기를 원했다고
    가정하자. *)

Lemma plus_comm3 :
  forall n m p, n + (m + p) = (p + m) + n.

(** 처음 보기에는 [plus_comm]을 두 번 적용하여 양 편을 일치하도록
    작성하여 이 정리를 증명할 수 있어야 할 것처럼 보인다. 하지만 두
    번째 [rewrite]는 첫 번째 적용한 결과를 되돌려 놓는 문제가 있다.
    *)

Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite plus_comm.
  (* 처음 시작했던 곳으로 돌아왔다... *)
Abort.

(** 이 문제를 해결하는 한 가지 간단한 방법은 (우리가 이미 아는
    방법만을 사용한다면) 우리가 원하는 정확한 그 곳에 다시 작성 전술을
    적용할 수 있도록 [plus_comm]의 특화 버전을 유도하기 위해서
    [assert]를 사용하는 것이다. *)

Lemma plus_comm3_take2 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  assert (H : m + p = p + m).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** 더 우아한 방법은 [plus_comm]을 적용하기를 원하는 인자에 직접
    적용하는 것이다.  마치 다형성 함수에 타입 인자를 적용하는 것과
    매우 흡사한 방법이다. *)

Lemma plus_comm3_take3 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.

(** 정리 이름을 인자로 받는 거의 모든 전술들을 이런 방식으로 "정리를
    함수처럼 사용"할 수 있다. 정리를 적용할 때 함수를 적용하는 것과
    동일한 추론 방법을 사용하는 점을 또한 주목하시오. 이렇게, 예를
    들어 인자로 와일드카드를 주어 추론되도록 하거나 정리의 어떤
    가정들을 묵시적으로 주어지도록 선언하는 것이 가능하다. 이 특징들을
    아래 증명에서 예시로 보여준다. *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** 이 절에서 보여준 관용 표현들의 더 많은 예들을 나중에 볼 것이다. *)

(* ################################################################# *)
(** * 콕 vs. 집합론 *)

(** 콕의 핵심 논리 부분, _Calculus of Inductive Constructions_,은
    정확하고 엄밀하게 증명을 쓰기 위해 수학자들이 사용한 다른 정형
    시스템과 비교할 때 몇 가지 중요한 측면에서 다르다. 예를 들어,
    종이와 연필로 증명하는 수학을 위한 가장 잘 알려진 기초는
    Zermelo-Fraenkel 집합론(ZFC)이다. 이 이론에서 수학적 객체는
    잠재적으로 많은 다른 집합들의 원소가 될 수 있다. 반면에 콕의
    논리에서 식은 기껏해야 한 가지 타입의 원소이다. 이 차이점은
    비형식적인 수학적 개념들을 표현하는 약간의 다른 방법들로 귀결되곤
    한다. 하지만 다른 방법이긴 하지만 대체로 꽤 자연스럽고 쉽게 작업할
    수 있다. 예를 들어 자연수 [n]은 짝수 집합에 속한다고 말하는 대신
    콕에서는 [ev : nat -> Prop]는 짝수를 기술하는 성질로 [ev n]이
    성립한다고 이야기 할 것이다.
    
    하지만 표준 수학적 추론으로 콕으로 변환하기 귀찮을 수 있고 때로는
    콕의 핵심 논리에 새로운 공리를 추가하지 않으면 심지어 그러한
    변환이 불가능한 경우 조차 있다. 이 두 세계들 사이의 가장 중요한
    차이점들 일부를 간략하게 논의하면서 이 장을 마친다. *)

(* ================================================================= *)
(** ** 함수 외연성 *)

(** 지금까지 살펴본 동치 주장은 대부분 귀납적 타입 ([nat], [bool],
    등등)의 원소들에 관한 것이었다. 하지만 콕의 동치 연산자는 다형성이
    있기 때문에 이 타입들의 원소들에 대해서만 가능한 것은 아니다. 특히
    두 _함수_가 서로 동일하다고 주장하는 명제를 작성할 수 있다. *)

Example function_equality_ex1 : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

(** 동일한 수학적 사례에서 두 함수 [f]와 [g]는 동일한 출력을 내면
    동일한 것으로 간주한다.

    (forall x, f x = g x) -> f = g

    이것을 _함수 외연성_ 원리라고 부른다.

    쉽게 설명하자면, "외연성 성질"은 객체의 관찰 가능한 동작에
    속한다. 마찬가지로 함수 외연성은 간단히 함수로부터 관찰할 수 있는
    것(예를 들어, 콕 식에서 함수를 적용한 다음 얻는 결과)으로 함수를
    구분하는 것을 의미한다.

    함수 외연성은 콕의 기본 공리가 아니다. 어떤 "합리적인" 명제들을
    증명할 수 없을 수도 있다는 것을 뜻한다. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

(** 하지만 [Axiom] 명령어를 사용하여 콕의 논리 핵심에 함수 외연성을
    추가할 수 있다. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** [Axiom]은 정리를 기술하고 [Admitted]를 사용하여 그 증명을 생략한
    것과 똑같은 효과를 낸다. 이 명령어를 사용하면 하지만 나중에 다시
    돌아와서 채우는 그런 것은 아니라는 것을 경고한다! *)

(** 이제 증명에서 함수 외연성을 사용할 수 있다. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

(** 콕 논리에 새로운 공리를 추가할 때 당연히 주의해야 한다. 왜냐하면
    새로운 공리는 콕을 _일관성을 잃게_ 만들 수 있기 때문이다. 즉,
    [False]를 포함한 모든 명제를 증명하도록 만들 수도 있다!

    불행히도 이 공리가 더해도 안전한지 판단할 수 있는 간단한 방법은
    없다.  일반적으로 특정 공리 조합의 일관성을 확인할 때 힘든 작업이
    필요하다.

    하지만 함수 외연성을 추가해도 _일관성을 유지한다고_ 알려져
    있다. *)

(** 특정 증명이 추가된 공리에 의존하는지 검사하기 위해서 [Print
    Assumptions] 명령어를 사용한다.  *)

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(** **** 연습문제: 별 네 개 (tr_rev)  *)
(** 리스트를 뒤집는 함수 [rev] 정의는 각 단계에서 [app]를 호출하는
    문제가 있다.  [app]를 리스트 길이에 비례해서 실행 시간이 걸리므로
    [rev]는 그 길이의 제곱에 해당하는 실행 시간이 걸린다. 다음 정의로
    이러한 문제를 개선할 수 있다.  *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** 이 버전을 _꼬리에서 재귀 함수를 호출_한다고 부른다. 왜냐하면 재귀
    함수 호출이 맨 마지막에서 수행하기 때문이다. 즉, 재귀 함수 호출
    다음에 [++]를 실행할 필요가 없다. 좋은 컴파일러는 이런 경우에 매우
    효율적인 코드를 생성할 것이다. 두 정의가 정말로 동일하다는 것을
    증명하시오. *)

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
(* 여기를 채우시오 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 명제와 부울 *)

(** 콕에서 논리적 사실을 표현하는 두 가지 다른 방법을 보았다. ([bool]
    타입의) _부울_을 사용하는 방법과 ([Prop] 타입의) _명제_를 사용하는
    방법이다.

    예를 들어, [n]이 짝수라고 주장하기 위해서 (1) [evenb n]은 [true]를
    리턴한다라고 말하거나 (2) [n = double k]인 어떤 [k]가 존재한다고
    얘기할 수 있다. 정말로 짝수에 대한 이 두 가지 개념들은
    동일하다. 이를 몇 가지 보조 정리들로 쉽게 보일 수 있다.

    부울 [evenb n]은 명제 [exists k, n = double k]를 _반영한다고_ 종종
    얘기한다. *)

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** 연습문제: 별 세 개 (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  (* 힌트: [Induction.v]의 [evenb_S] 보조 정리를 사용하시오. *)
  (* 여기를 채우시오 *) Admitted.
(** [] *)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

(** 비슷하게 두 숫자 [n]과 [m]이 같다고 말하기 위해서 (1) [beq_nat n
    m]이 [true]를 리턴한다고 말하거나 (2) [n = m]이라고 말할 수
    있다. 이 두 개념들은 동일하다. *)

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

(** 순수한 논리적 관점에서 어떤 주장을 부울과 명제로 동일하게 작성할
    수 있다고 하더라도 _증명 과정_에서 동일할 필요는 없다. 동등성은 한
    가지 극단적인 예를 제공한다.  [beq_nat n m = true]를 알고 있다고
    해도 [n]과 [m]이 관여한 증명에 일반적으로 직접적인 도움이 되지
    못한다. 하지만 이 문장을 동등한 [n = m] 형태로 바꾸면 이 것을
    가지고 다시 작성 전술에 활용할 수 있다.

    짝수의 경우에도 흥미롭다. [even_bool_prop] (즉, [evenb_double],
    명제에서 부울식 주장으로 향하는)의 역 방향을 증명할 때 [k]에 대한
    귀납법을 간단히 사용했다.  반면에 역 ([evenb_double_conv]
    연습문제)은 현명한 일반화가 필요했다.  왜냐하면 [(exists k, n =
    double k) -> evenb n = true]를 직접 증명할 수 없기 때문이다.

    이 예제들에서 명제로 주장하는 것은 부울 주장보다 더
    유용하다. 하지만 항상 그러한 것은 아니다. 예를 들어, 함수 정의에서
    일반적인 명제가 참인지 거짓인지 테스트할 수 없다.  그 결과 다음
    코드를 콕이 거절한다. *)

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** 콕은 [bool] (또는 두 원소를 갖는 어떤 다른 귀납적 타입) 원소를
    기대했지만 [n = 2]가 [Prop] 타입이라고 불평할 것이다.  이 에러
    메시지를 내는 이유는 콕의 핵심 언어의 _계산적인_ 성질과 관련이
    있다. 콕이 표현할 수 있는 모든 함수는 계산 가능하고 항상
    종료하도록 핵심 언어를 설계하였다. 이렇게 설계한 한 가지 이유는 콕
    증명으로부터 실행 가능한 프로그램을 추출하기 위한 것이다. 그 결과
    콕에서 [Prop]은 어떤 주어진 명제가 참인지 거짓인지 판단하는
    보편적인 경우 별 분석 연산을 _가지고 있지 않다_. 왜냐하면 그러한
    연산을 허용하면 계산할 수 없는 함수를 작성할 수 있기 때문이다.

    비록 일반적인 계산 가능하지 않는 성질들을 부울 계산으로 나타낼 수
    없지만 많은 _계산 가능한_ 성질들조차 [bool]보다 [Prop]을 사용해서
    표현하는 것이 더 쉽다는 것을 주목할만하다. 왜냐하면 콕에서 재귀
    함수를 정의하는데 큰 제약이 있기 때문이다. 예를 들어 다음 장에서
    [Prop]을 사용하여 정규식과 문자열을 매칭 하는 성질을 어떻게
    정의하는지 보여준다. [bool]을 가지고 똑같은 것을 한다면 정규식
    매치 함수를 작성하는 것과 다름이 없을 것인데, 더 복잡하고 이해하기
    어렵고, 추론에 활용하는 것이 더 어려울 것이다.

    역으로 부울을 가지고 사실을 기술하는 것의 중요한 부수적인 이점은
    콕 식의 계산을 통해 어떤 증명을 자동화할 수 있다는 것이다.  이
    기법은 _반사에 의한 증명_이라 알려져 있다. 다음 문장을
    고려해보자. *)

Example even_1000 : exists k, 1000 = double k.

(** 이 사실을 가장 직접적으로 증명하는 것은 [k]의 값을 명확히 주는 것이다. *)

Proof. exists 500. reflexivity. Qed.

(** 반면에 해당하는 부울 기반 문장에 대한 증명은 한층 더 간단하다. *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

(** 흥미로운 점은, 두 개념이 동일하기 때문에 500을 명시적으로 언급하지
    않고 부울 기반 문장을 사용하여 앞의 명제를 증명할 수 있다는
    점이다. *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(** 이 경우 증명 크기에 관하여 얻은 것이 비록 없지만 더 큰 증명의 경우
    반사를 사용하면 훨씬 더 간단하게 증명할 수 있곤 한다. 극단적인
    예로써 유명한 _4색 정리_에 대한 콕 증명에서 반사를 사용하여 부울
    계산의 수백 가지 다른 경우들을 분석하는 것을 줄였다. 반사에 대해
    매우 깊이 설명하지 않지만 부울과 일반적인 명제의 보완적인 장점들을
    보여주는 좋은 예이다.
 *)

(** **** 연습문제: 별 두 개 (logical_connectives)  *)
(** 다음 보조 정리들은 이 장에서 공부한 명제의 연결자들을 해당하는
    부울 연산과 연관시킨다. *)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* 여기를 채우시오 *) Admitted.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 한 개 (beq_nat_false_iff)  *)
(** 다음 정리는 [beq_nat_true_iff]의 또 다른 "부정" 형식이다. 이것은
    어떤 상황에서 더 편리하다 (나중에 예제를 살펴 볼 것이다). *)

Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개 (beq_list)  *)
(** 어떤 타입 [A]의 원소들이 동일한지 비교하는 부울 연산자 [beq]에
    대해 [A] 타입 원소를 갖는 리스트가 동일한지 비교하는 함수
    [beq_list beq]를 정의할 수 있다. 아래의 [beq_list] 함수 정의를
    완성하시오. 그 정의가 올바른지 확인하기 위해 [beq_list_true_iff]
    보조 정리를 증명하시오. *)

Fixpoint beq_list {A : Type} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* 이 줄을 ":= _여러분의 정의_"로 다시 작성하시오 *). Admitted.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
(* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 두 개, 추천 (All_forallb)  *)
(** [Tactics] 장의 연습문제 [forall_exists_challenge]에서 [forallb]
    함수를 기억해보자. *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** 위 연습문제의 [forallb]를 [All]를 연관짓는 아래의 정리를
    증명하시오. *)

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* 여기를 채우시오 *) Admitted.

(** 함수 [forallb]의 중요한 성질들 중에 이 명세로 표현되지 않는 것이
    있는가?  *)

(* 여기를 채우시오 *)
(** [] *)

(* ================================================================= *)
(** ** 고전적 vs. 건설적 논리 *)

(** 명제 [P]가 성립하는지 검사하는 것은 가능하지 않다고
    하였다. _증명_!에도 유사한 제약이 적용된다는 것에 놀랄 수도
    있다. 달리 설명하면 다음의 직관적인 유추 원리를 콕에서 유도할 수
    없다. *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** 왜 그러한지 과정 측면에서 이해하자면 [P \/ Q] 형태의 문장을
    증명하기 위해 [left]와 [right] 전술을 사용하였음을 기억하자. 각각
    논리합의 해당하는 편이 성립하는 증명을 가지고 있다는
    요구한다. 하지만 [excluded_middle]에서 전칭 한정 [P]의 경우
    _임의의_ 명제이고 그 것에 대해 아무것도 알지 못한다.  [left]와
    [right] 중에 어느 것을 적용할 지 선택할 충분한 정보가 없다.
    왜냐하면 콕은 함수 안에서 [P]가 성립하는지 여부를 기계적으로
    결정하기 위해서 충분한 정보를 갖고 있지 않는 것이기 때문이다. *)

(** 하지만 [P]를 어떤 부울 식 [b]로 투영할 수 있다면 [P]가 성립하는지
    여부를 아는 것은 매우 쉽다. [b]의 값을 들여다 보기만 하면 된다. *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

(** 특히, 자연수 [n]과 [m]에 대한 [n = m] 식에 대해서 excluded_middle
    정의는 성립한다.  *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  symmetry.
  apply beq_nat_true_iff.
Qed.

(** 콕에 일반적인 excluded_middle이 성립하지 않는 것에 대해 이상하게
    생각할 수도 있다. 왜냐하면 결국 모든 주장은 참 또는 거짓이어야
    하기 때문이다.  그럼에도 불구하고 이 것을 가정하지 않는 장점이
    있다. 콕의 문장은 표준 수학에서 유사한 문장보다 더 강한 주장을
    만들 수 있기 때문이다. 좋은 예로 [exists x. P x]를 콕에서 증명하면
    [P x]를 증명하는 [x]의 값을 명시적으로 보여줄 수 있다.  다르게
    설명하면 존재에 대한 모든 증명은 반드시 _건설적_이다. *)

(** excluded_middle을 가정하지 않는 콕과 같은 논리를 _건설적 논리_라고
    부른다.

    임의의 명제에 대해 excluded_middle이 성립하는 ZFC와 같은 더 자주
    사용하는 논리 시스템을 _고전적_이라고 부른다. *)

(** 다음 예는 exlcluded_middle을 가정하면 왜 비 건설적인 증명이 될
    수도 있는지를 보여준다.

    _주장_: [a ^ b]가 유리수인 무리수 [a]와 [b]가 존재한다.

    _증명_: [sqrt 2]가 무리수라는 것을 증명하는 것은 어렵지 않다. 만일
    [sqrt 2 ^ sqrt 2]가 유리수라면 [a = b = sqrt 2]를 취하는 것으로
    증명할 수 있다. 만일 유리수가 아니라면 [a = sqrt 2 ^ sqrt 2]라
    하고 [b = sqrt 2]로 놓자. [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) =
    sqrt 2 ^ 2 = 2]. []
    
    여기서 무슨 일이 벌어졌는지 이해하는가? [sqrt 2 ^ sqrt 2]가
    유리수인 경우와 그렇지 않은 경우를 excluded_middle을 사용하여
    분리해서 고려하였다. 하지만 어느 것이 성립하는지 알지 못한다! 바로
    그 것 때문에 그러한 [a]와 [b]가 존재하는 것을 아는 문제를 우회해서
    매듭지었지만 실제 값이 무엇인지 결정할 수 없다 (적어도 이 논법을
    사용하여).

    건설적 논리만큼 유용하지만 한계를 가지고 있다. 고전적 논리에서
    쉽게 증명할 수 있지만 훨씬 복잡한 건설적 증명을 필요로 하는 많은
    문장들이 있다. 그리고 건설적 방법으로 전혀 증명할 수 없다고 알려진
    것도 있다! 운 좋게도 함수 외연성 처럼 excluded_middle은 콕의
    논리와 호환 가능하다고 알려져 있어서 공리로 안전하게 추가할 수
    있다. 하지만 이 책에서는 그것을 필요로 하지 않을 것이다. 왜냐하면
    우리가 다루는 결과들은 건설적 논리로 무시할만한 추가 비용으로 모두
    증명할 수 있기 때문이다.

    건설적 추론에서 어떤 증명 기법들을 피해야 하는지 이해하는데 약간의
    연습이 필요하다. 하지만 모순에 의한 주장은 특히 비건설적 증명을
    초래하는 것으로 악명이 높다. 전형적인 예를 살펴보자. 어떤 성질
    [P]를 갖는 [x]가 존재한다는 것(즉, [P x])를 증명하기를 원한다고
    가정하자.  우리의 결론이 거짓이라고 가정하면서 시작한다. 즉
    [~exists x, P x].  이 가설로부터 [forall x, ~ P x]를 유도하는 것은
    어렵지 않다. 이 중간 단계의 사실이 모순을 일으킨다는 것을 보일 수
    있다면 [P x]를 만족하는 [x]의 값을 결코 보이지 않고도 존재 증명에
    도달한다!

    여기에서 건설적 관점에서 바라볼 때 기술적 결함은 [~ ~(exists x, P
    x)] 증명을 사용하여 [exists x, P x]를 증명하였다고 주장한
    것이다. 임의의 문장에서 이중 부정을 제거하는 것을 허용하는 것은
    excluded_middle을 가정하는 것과 동일하다.  아래의 연습문제에서
    보여준다. 이렇게 이러한 논법은 새로운 공리를 추가하지 않고 콕에서
    표현할 수 없다. *)

(** **** 연습문제: 3 stars (excluded_middle_irrefutable)  *)
(** The consistency of Coq with the general excluded middle axiom
    requires complicated reasoning that cannot be carried out within
    Coq itself.  However, the following theorem implies that it is
    always safe to assume a decidability axiom (i.e., an instance of
    excluded middle) for any _particular_ Prop [P].  Why? Because we
    cannot prove the negation of such an axiom; if we could, we would
    have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)

Theorem excluded_middle_irrefutable:  forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개, 고급 (not_exists_dist)  *)
(** 다음 두 주장이 동일하다는 것은 바로 고전적 논리의 정리이다:

    ~ (exists x, ~ P x) forall x, P x

    위의 [dist_not_exists] 정리는 이 등식의 한쪽만
    증명한다. 흥미롭게도 다른 방향은 건설적 논리에서 증명할 수
    없다. 이 연습문제에서 당신이 할 일은 그 다른 방향이
    excluded_middle에서 부터 함축된다는 것을 보이는 것이다. *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 다섯 개, 선택사항 (classical_axioms)  *)
(** 도전적인 사람은 Bertot와 Casteran이 작성한 책 (p. 123)에서 가져온
    연습문제를 풀어보자. 다음 네 개의 문장들 각각은
    [excluded_middle]와 함께 고전적 논리를 특징짓는 문장이라고 간주할
    수 있다. 콕으로는 어떤 것도 증명할 수 없다. 하지만 고전적 논리로
    증명하기를 원한다면 네 개 중 어떠한 것 하나를 일관성 있게 추가할
    수 있다.

    모든 다섯 개 명제 (아래 네 개와 [excluded_middle])가 동등함을
    증명하시오. *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(* 여기를 채우시오 *)
(** [] *)

(** $Date: 2017-08-22 17:13:32 -0400 (Tue, 22 Aug 2017) $ *)
