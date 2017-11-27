(** * IndProp: 귀납적으로 정의한 명제 *)

Require Export Logic.

(* ################################################################# *)
(** * 귀납적으로 정의한 명제 *)

(** [Logic] 장에서 논리곱, 논리합, 한정자를 포함하여 명제를 작성하는
    방법들을 살펴보았다. 이 장에서 새로운 도구 _귀납적 정의_를 명제
    작성 방법에 도입한다.

    숫자 [n]이 짝수라고 서술하는 두 가지 방법을 돌이켜보자. (1) [evenb
    n = true]라고 말하거나 (2) [exists k, n = double k]라고 말할 수
    있다. 또 다른 가능한 방법은 다음 규칙들로부터 짝수에 대한 정의를
    만들 수 있다.

       - 규칙 [ev_0]: 숫자 [0]은 짝수. 규칙 [ev_SS]: 만약 [n]이 짝수면 
       - [S (S n)]은 짝수.  *)

(** 짝수에 대한 이 정의를 활용하는 법을 설명하기 위해 [4]가 짝수라는
    것을 증명하기 위해 이 정의를 사용해보자. 규칙 [ev_SS]로 [2]가
    짝수인 것을 보이기에 충분하다. 그다음 다시 규칙 [ev_SS]로 증명을
    보장한다.  필요한 가정은 [0]이 짝수라는 사실인데, 규칙 [ev_0]으로
    직접 증명할 수 있다. *)

(** 앞으로 남은 강의를 진행하는 동안 이런 정의를 많이 만나게 될
    것이다. 비형식적으로 논의할 때는 읽고 쓰기 쉬운 가벼운 표기법을
    사용하는 것도 도움이 될 것이다. _추론 규칙_은 이러한 가벼운
    표기법이다.  *)
(**

                              ------------                        (ev_0)
                                 ev 0

                                  ev n
                             --------------                      (ev_SS)
                              ev (S (S n))
*)

(** 앞서 텍스트로 작성한 각 규칙은 추론 규칙으로 여기 다시 작성한다.
    이 추론 규칙은 줄 위의 _전제_가 모두 성립하면 줄 아래 _결론_을
    내린다고 읽을 수 있다. 예를 들어, [ev_SS] 규칙은 [n]이 [ev]를
    만족하면 [S (S n)]도 만족한다고 말하고 있다. 줄 위에 아무런 전제가
    없다면 결론은 조건없이 성립한다.

    이 규칙들을 사용한 증명을 규칙을 적용하여 만든 _증명 트리_로
    표현할 수 있다.  다음은 [4]가 짝수라는 위의 증명을 어떻게 기술할
    수 있을지 설명한다. *)
(**

                             ------  (ev_0)
                              ev 0
                             ------ (ev_SS)
                              ev 2
                             ------ (ev_SS)
                              ev 4
*)

(** 이것을 예를 들어 "스택"이라 부르지 않고 왜 "나무"라 할까?  그
    이유는 일반적으로 추론 규칙은 여러 전제를 가질 수 있기 때문이다.
    아래에서 그러한 예들을 만나게 될 것이다. *)

(** 이것을 모두 합해보면 짝수에 대한 정의를 [Inductive] 선언을
    사용하여 콕의 형식적인 정의로 변환할 수 있다. 이때 각 생성자는
    특정 규칙에 대응한다. *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

(** 이 정의는 이전에 [Inductive]를 사용한 사례들과 한 가지 중요한
    점에서 다르다. 그 결과가 [Type]이 아니라 [nat]에서 [Prop]로 가는
    함수라는 것이다. 즉, 숫자의 성질이다. [list]와 같이 [Type -> Type]
    타입을 갖는 함수를 만드는 귀납적 정의들을 이미 보아왔다. 여기서
    새로운 것은 [ev]의 [nat] 인자가 콜론 _오른쪽_에 _이름 없이_
    나타났기 때문에 다른 생성자들의 타입에 다른 값을 취하는 것을
    허용하는 것이다.  [ev_0]의 타입에는 [0]을, [ev_SS]의 타입에는 [S
    (S n)]을 사용하고 있다.

    이와 대조적으로 [list] 정의에서는 [X] 매개변수를 콜론 _왼쪽_에
    _전역적으로_ 이름을 부여했고, [nil]과 [cons]의 결과가 ([list X])로
    동일하도록 만들었다. 만일 [ev]를 정의하면서 그 왼쪽에 [nat]을
    도입하려고 한다면 다음의 에러가 발생할 것이다.  *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> 에러: 귀납적 타입 n의 매개변수는 생성자 타입에서 속박 변수로 사용할
        수 없다.  *)

(** (여기서 "매개변수"는 [Inductive] 정의에서 콜론 왼쪽에 나타난
    인자를 가리키는 콕의 용어이다. 콜론 오른쪽에 나타난 인자를 지칭할
    때 "인덱스"를 사용한다.)  *)

(** [ev] 정의를 [ev_0 : ev 0]과 [ev_SS : forall n, ev n -> ev (S (S
    n))]이라는 두 가지 정리들과 함께 콕 성질 [ev : nat -> Prop]를
    정의하는 것으로 생각할 수 있다. 이러한 "생성자 정리들"은 증명한
    정리들과 동일한 상태를 갖는다. 특히 특별한 숫자들에 대해 [ev]를
    증명하기 위해 콕의 [apply] 전술에서 이 규칙 이름들을 지정할 수
    있다. *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... 또는 아래와 같이 함수 적용 구문을 사용할 수 있다. *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** [ev]를 포함하는 가정들을 갖는 정리들을 증명할 수도 있다.  *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** 더 일반적으로 임의 수에 2를 곱하면 짝수가 된다는 것을 보일 수 있다.  *)

(** **** Exercise: 별 한 개 (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 증명에서 증거를 사용하기 *)

(** 숫자가 짝수임을 보이는 증거를 _만드는 것_과 함께 그러한 증거에
    대해 _추론하는 것_도 가능하다.

    [Inductive] 선언으로 [ev]를 도입하여 생성자 [ev_0]와 [ev_SS]가
    어떤 숫자가 짝수임을 보이는 증거를 만드는 유효한 방법일 뿐만
    아니라 이 두 생성자가 ([ev] 관점에서) 이 증거를 만드는 _유일한_
    방법이라는 것을 콕에게 알린다. *)

(** 다르게 표현하자면, [ev n]을 주장하는 증거 [E]가 있다면 [E]는 반드시 
    두 가지 형태들 중 하나 이어야 한다. 
  
     - [E]는 [ev_0] (그리고 [n]은 [O]) 또는
     - [E]는 [ev_SS n' E'] (그리고 [n]은 [S (S n')]이고 [E']은 
       [ev n']에 대한 증거이다)  *)

(** 따라서 귀납적 데이터를 다루는 방식과 똑같이 [ev n] 형태의 가정을
    분석할 수 있어야 한다는 것이다. 특히 그러한 증거에 대해 _귀납법_과
    _경우 별 분석_으로 주장할 수 있어야 한다. 실제로 무엇을 뜻하는지
    두 세 가지 예제를 살펴 보자. *)

(* ================================================================= *)
(** ** 증거에 대한 인버전 *)

(** 숫자 [n]에 대한 사실을 증명하는데 가정으로 [ev n]이 주어져 있다고
    하자.  [inversion] 전술을 사용하여 [n]에 대한 경우 별 분석을
    수행하여 [n = 0]인 경우와 어떤 [n']에 대해서 [n = S n']인 경우로
    분리된 부분 목적들을 만드는 방법을 이미 안다.  하지만 어떤
    증명에서는 이 방법 대신 증거 [ev n]을 _직접_ 분석하기를 원할 수
    있다.

    [ev] 정의에 따라 두 가지 경우들을 고려한다.

    - 그 증거가 [ev_0] 형태라면 [n = 0]이라는 것을 안다.
   
    - 만일 그렇지 않다면 그 증거는 [ev_SS n' E'] 형태이고 [n = S (S
      n')]이며 [E']은 [ev n']에 대한 증거이어야 한다.  *)

(** 콕에서 (다시) [inversion] 전술을 사용하여 이러한 추론을 진행할 수
    있다. [inversion]으로 생성자들을 포함하는 등식에 대해 추론하는 것
    뿐만 아니라 귀납적으로 정의한 명제에 대해서도 경우 별로 분석할 수
    있다. 이렇게 이 전술을 사용하면 그 구문은 [destruct]와
    비슷하다. [|]로 분리된 식별자 리스트를 이 전술에 지정하여 각각의
    가능한 생성자의 인자들에 이름을 붙인다.  *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** 위 콕 증명에서 인버전 추론이 어떻게 동작하는지 풀어 설명하면
    다음과 같다.

    - [ev_0] 형태 증거가 주어지면 [n = 0]이라는 것을 안다. 그러므로
      [ev (pred (pred 0))]이 성립하는 것을 보이는 것으로 충분하다.
      [pred] 정의에 따라 [ev 0]을 보이는 것과 동일하며 [ev_0]에 의해
      바로 증명할 수 있다.

    - 그렇지 않으면, 이 증거는 반드시 [ev_SS n' E'] 형태이고 [n = S (S
      n')]이며 [E']은 [ev n']에 대한 증거이어야 한다. 그다음에 [ev
      (pred (pred (S (S n'))))]이 성립함을 보여야 한다. 이를 단순하게
      변환한 다음 [E']으로 바로 증명할 수 있다. *)

(** 이 특별한 증명 사례는 [inversion]을 [destruct]로 바꾸어도 증명
    가능하다.  *)

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** 두 전술을 사용한 증명들의 차이는, 복잡한 식(변수 한개로 이루어진
    식과 반대로)에 적용된 귀납적 성질을 나타내는 가정에 대해서는
    [inversion]이 더 편리하다는 것이다. 여기 구체적인 예를 보자.
    [ev_minus2]의 변형으로 다음을 증명하기를 원한다고 가정하자. *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.

(** 직관적으로 가정에 대한 증거는 [ev_0] 생성자가 아니라는 것을
    안다. 왜냐하면 [O]와 [S]는 [nat] 타입의 다른 생성자들이기
    때문이다. 따라서 [ev_SS]가 적용할 유일한 경우이다. 불행히도
    [destruct]는 이러한 상황을 고려하지 않기 때문에 두 개의 부분
    목적들을 여전히 생성한다. 더 심각한 것은 이 전술을 사용해면 최종
    목적이 변하지 않아서 이 증명을 완성하는데 어떠한 유용한 정보도
    주지 않는 것이다.  *)

Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* 아무런 가정없이 [n]이 작수임을 증명해야 한다! *)
Abort.

(** 정확히 어떤 상황이 벌어진 것인가? [destruct]를 사용하면 각 성질의
    인자가 나타난 곳을 모두 각 생성자에 대응하는 값들로 바꾸는 효과가
    있다. [ev_minus2']의 경우에는 이 인자 [n]이 최종 목적에 바로
    사용되었으므로 이렇게 바꾸는 것으로 충분하다. 하지만 [evSS_ev]의
    경우에 대체되는 식 ([S (S n)])이 어디에도 다시 나타나지 않기
    때문에 도움이 되지 않는다. *)

(** 반면에 [inversion] 전술로 (1) 첫번째 경우가 적용되지 않고, (2)
    [ev_SS]에 나타난 [n']이 [n]과 동일해야 한다는 것을 찾아낼 수 있다.
    이 방법으로 증명을 완성한다.  *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* 이제 [E = ev_SS n' E'] 경우를 고려한다. *)
  apply E'.
Qed.

(** [inversion]을 사용하여 귀납적 성질을 포함하는 "명백하게 모순인"
    가정들에 폭발 원리를 적용할 수도 있다. 예를 들어: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

(** **** 연습문제: 별 한 개 (inversion_practice)  *)
(** [inversion]을 사용하여 다음 결과들을 증명하시오. *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** 여기서 [inversion]을 사용한 방법은 처음에는 다소 불가사의하게 보일
    수 있다. 지금까지는 등식 형태의 명제에 대해서만 [inversion]을
    사용하며 생성자의 단사 성질을 사용하거나 다른 생성자들을
    구별하였다.  하지만 귀납적으로 정의된 명제들에 대한 증거를
    분석하는 데에도 [inversion]을 적용할 수 있음을 여기서 확인한다.

    [inversion]이 동작하는 일반적인 방법을 설명한다. 이름 [I]는 현재
    문맥에 있는 가정 [P]를 참조하고 [P]는 [Inductive] 선언으로
    정의되었다고 가정하자.  그렇다면 [P]의 각 생성자에 대해 [inversion
    I]는 [P]를 증명하기 위해 사용했을 수 있는 이 생성자의 특정 조건
    그대로를 [I]가 나타난 모든 곳에 대체하여 부분 목적을 생성한다. 이
    부분 목적들 중 일부는 스스로 모순일 수 있다. [inversion]은 이러한
    부분 목적들을 버린다. 남은 부분 목적들은 원래 목적이 성립하려면
    증명되어야 할 경우들을 나타낸다. [inversion] 전술로 남은 부분
    목적을 위해 [P]에 주어진 인자들에 대해 성립해야 할 증명 문맥으로
    모든 등식들을 추가한다 (예를 들어 [evSS_ev] 증명에서 [S (S n') =
    n]). *)

(** 위의 [ev_double] 연습문제는 짝수에 대한 우리의 새로운 개념은 이전
    두 연습문제들로 부터 유도할 수 있음을 보인다. ([논리] 장에서
    [even_bool_prop]에 의해 서로 동일한 것을 이미 알고 있다. 세 개
    모두가 일치하는 것을 보이려면 다음 보조 정리만 필요하다. *)

Lemma ev_even_firsttry : forall n,
  ev n -> exists k, n = double k.
Proof.
(* 수업에서 다루었음 *)

(** 경우별 분석이나 [n]에 대한 귀납법으로 증명하는 것을 시도할 수도
    있다.  하지만 [ev]는 전제에 나타나있기 때문에 이전에 논의한 바와
    같이 이 전략은 분명히 막다른 골목에 다다를 것이다. [ev]의 증거에
    대한 인버전을 먼저 시도하는 것이 나은 것 처럼 보인다. 정말로 첫
    번째 경우는 사소하게 해결될 수 있다.  *)

  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.

(** 불행히도 두 번째 경우는 더 어렵다. [exists k, S (S n') = double
    k]를 보일 필요가 있지만, 오직 사용할 수 있는 가정은 [ev n']이
    성립함을 보이는 [E']이다. 이 가정은 바로 사용되는 것은 아니기
    때문에 막힌 것 같고 [E]에 대한 경우 별 분석을 시간 낭비였던 것으로
    보인다.

    두 번째 목적을 더 가까이 살펴보면 흥미로운 일이 발생했음을 알 수
    있다.  [E]에 대한 경우 별 분석을 수행하여 원래 결과를 [ev]: [E']을
    증명하는 _다른_ 증명을 포함하는 유사한 결과로 변환할 수 있었다. 더
    형식적으로 다음을 증명하면 전체 증명을 마칠 수 있다.

        exists k', n' = double k',

    이 문장은 원래 문장과 동일하지만 [n] 대신 [n']으로
    바뀌었다. 정말로 콕에서 이 중간 결과로 충분함을 보이는 것은 어렵지
    않다. *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* 원래 목적으로 새로운 목적으로 환원시킨다. *)

Admitted.

(* ================================================================= *)
(** ** 증거에 대한 귀납법 *)

(** 이 제목이 익숙해 보이면 우연이 아니다.  귀납법을 요구하는 결과들을
    증명하려고 경우 별 분석을 사용하려고 할 때 [Induction] 장에서
    비슷한 문제들을 맞닥뜨렸다. 그리고 다시 한번 그
    해답은... 귀납법이다!

    증거에 대한 [induction]의 동작 방식은 데이터에 대한 동작 방식과
    같다.  그 증거를 쌓아가기 위해 사용했을 수 있는 각 생성자의 부분
    목적을 콕이 만들고 증명하려는 성질이 재귀적으로 나타날때 마다
    귀납적 가정을 제공한다. *)

(** 현재 보조 정리를 다시 시도해 보자. *)

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       IH와 함께: exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(** 콕은 [ev]의 정의에서 단일 재귀 형태가 나타난 부분 [E']에 대응하는
    [IH]를 만든 것을 볼 수 있다. [E']에 [n']이 나타나기 때문에 귀납적
    가정은 [n]이나 어떤 다른 숫자가 아닌 [n']에 대한 것이다. *)

(** 짝수에 대한 두 번째와 세 번째 정의가 동일함을 이제 증명한다. *)

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** 나중에 보게 되듯이 증거에 대한 귀납법은 많은 분야를 거쳐서
    반복해서 나타나는 기법이다. 특히 많은 성질들을 귀납적으로 정의하는
    경우인 프로그래밍언어 의미를 형식화할 때 많이 사용한다. *)

(** 이 방법에 익숙해지도록 이 방법을 사용하는 간단한 예를 보여준다.
*)

(** **** 연습문제: 별 두 개 (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 네 개, 고급, 선택사항 (ev_alternate)  *)
(** 일반적으로 어떤 성질을 귀납적으로 정의하는 방법은 여러 가지이다. 
    다음은 [ev] 성질을 다소 복잡하게 정의한 예이다. *)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

(** 이 정의가 원래 정의와 논리적으로 동치임을 증명하시오. (귀납적 단계에 
    이르면 이전 정리를 보고 싶어할 수도 있다.) *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
 (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개, 고급, recommended (ev_ev__ev)  *)
(** 여기서 귀납법을 적용하기에 적절한 것을 찾는 것이 다소 어려울 수
    있다.  *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 세 개, 선택사항 (ev_plus_plus)  *)
(** 이 연습문제는 이전에 증명해놓은 보조 정리를 적용하기만 하면 된다.
    다시 작성하는 전술로 증명한 것 중에 어떤 것은 지루할 수 있지만
    귀납법이나 경우 별 분석이 필요하지 않다.  *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 귀납적 관계 *)

(** 숫자를 매개변수로 하는 명제 (예를 들어 [ev])는 _성질_로 해석할 수
    있다.  즉 [nat]의 부분 집합을 정의하여 이 집합에 속하는 숫자는
    명제가 성립한다.  똑같은 방식으로 두 인자를 받는 명제를 _관계_로
    해석할 수 있다. 명제가 성립하도록 하는 쌍들의 집합을 정의한다. *)

Module Playground.

(** 숫자에 관한 "작거나 같다"라는 관계가 한가지 유용한 예이다. *)

(** 다음 예는 꽤 직관적이다. 한 숫자가 다른 숫자보다 작거나 같음을
    보이는 증거를 제시하는 두 가지 방법이 있다고 말한다. 두 숫자가
    같거나 또는 첫 번째 숫자가 두 번째의 이전 숫자 보다 작거나 같다는
    증거를 제시한다. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** 생성자 [le_n]과 [le_S]를 사용하여 [<=]에 대한 사실들을 증명하는
    것은 위의 [ev]처럼 성질에 대해 증명하는 것과 똑같은 패턴을
    따른다. [<=] 목적 (예를 들어, [3<=3] 또는 [3<=6]을 보이기 위해)을
    증명하기 위해 이 생성자들을 [apply]할 수 있고, 문맥에 있는 [<=]
    가정 (예를 들어 [(2 <= 1) -> 2+2=5]를 증명하기 위해서)에서 정보를
    추출하기 위해서 [inversion] 같은 전술을 사용할 수 있다. *)

(** 여기서 이 정의가 제대로 이루어졌는지 검사한다. (비록 처음 몇몇
    강의에서 작성하였던 테스트 함수들에 대해 제공했던 것과 동일한
    종류의 간단한 "유닛 테스트"이지만 그 증명을 명시적으로 만들어야
    한다. [simpl]과 [reflexivity] 전술들은 검사하는데 더 이상 도움이
    되지 않는다. 왜냐하면 그 증명들은 단지 계산을 단순화하는 것이
    아니기 때문이다.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* 수업에서 다루었음 *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* 수업에서 다루었음 *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* 수업에서 다루었음 *)
  intros H. inversion H. inversion H2.  Qed.

(** "엄격히 작은" 관계 [n < m]은 이제 [le]에 관하여 정의할 수 있다.  *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** 여기 숫자에 대한 두 세가지 더 간단한 관계를 정의하였다.  *)

Inductive square_of : nat -> nat -> Prop :=
  | sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** 연습문제: 별 두 개, 선택사항 (total_relation)  *)
(** 자연수의 모든 쌍에 대해 성립하는 귀납적 이진 관계
    [total_relation]을 정의하시오. *)

(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 두 개, 선택사항 (empty_relation)  *)
(** (숫자에 관하여) 결코 성립하지 않는 귀납적 이진 관계
    [empty_relation]을 정의하시오. *)

(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 세 개, 선택사항 (le_exercises)  *)
(** [<=]과 [<] 관계에 대한 많은 사실들이 여기 있다. 이 강의에서 나중에
    필요하다. 이 사실들에 대한 증명은 좋은 실용적인 연습문제가 된다.
 *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 (* 여기를 채우시오 *) Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* 여기를 채우시오 *) Admitted.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  (* 여기를 채우시오 *) Admitted.

(** 힌트: 다음 정리는 [m]에 대한 귀납법으로 가장 쉽게 증명될 수 있다. *)

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  (* 여기를 채우시오 *) Admitted.

(** 힌트: 이 정리는 [induction]을 사용하지 않고 쉽게 증명할 수 있다. *)

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  (* 여기를 채우시오 *) Admitted.

(** **** 연습문제: 별 두 개, 선택사항 (leb_iff)  *)
Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

Module R.

(** **** 연습문제: 별 세 개, 추천 (R_provability)  *)
(** 삼 중 관계, 사 중 관계 등을 이진 관계와 동일한 방식으로 정의할 수 있다.
    예를 들어, 숫자에 대한 다음과 같은 삼 중 관계를 보자.
 *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - 다음 명제들 중 어느 것이 증명 가능한가?
      - [R 1 1 2]
      - [R 2 2 6]


    - 정의 [R]에서 생성자 [c5]를 빼면 증명 가능한 명제 집합이 변할까? 
      (한 문장으로) 간단히 답을 하시오.

    - 정의 [R]에서 생성자 [c4]를 빼면 증명 가능한 명제 집합이 변할까? 
      (한 문장으로) 간단히 답을 하시오.

(* 여기를 채우시오 *)
[]
*)

(** **** 연습문제: 별 세 개, 선택사항 (R_fact)  *)
(** 위의 관계 [R]은 사실 익숙한 함수를 인코딩한다. 어떤 함수인지 
    맞추어보시오. 그런 다음 콕에서 다음 동치를 기술하고 증명하시오. *)

Definition fR : nat -> nat -> nat
  (* 이 줄을 당신의 정의로 대체하시오 *). Admitted.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
(* 여기를 채우시오 *) Admitted.
(** [] *)

End R.

(** **** 연습문제: 별 네 개, 고급 (subsequence)  *)
(** 첫번째 리스트의 모든 원소들이 동일한 순서로 두번째 리스트에
    나타나면 첫번째 리스트는 두 번째 리스트의 _부분 순열_이다.  두
    번째 리스트에는 추가적으로 어떤 원소들이 사이 사이에 포함될 수
    있다.  예를 들어,

      [1;2;3]

    은 아래 리스트들의 부분 순열이다.

      [1;2;3] [1;1;1;2;2;3] [1;2;7;3] [5;6;1;9;9;2;7;3;8]

    하지만 다음 리스트들 중 어느 것의 부분 순열도 _아니다_.

      [1;2] [1;3] [5;6;2;1;7;3;8].

    - [list nat]에 관한 귀납적 명제 [subseq]를 정의해서 부분 순열이
      의미하는 바를 표현해보시오. (힌트: 세 가지 경우가 필요할
      것이다.)

    - 부분 순열이 반사적임을 기술하는 [subseq_refl]을 증명하시오. 즉,
      어떠한 리스트도 자신의 부분 순열이다.

    - 어떤 리스트 [l1], [l2], [l3]에 대해 [l1]이 [l2]의 부분 순열이면
      [l1]이 또한 [l2 ++ l3]의 부분 순열임을 기술하는 [subseq_app]를
      증명하시오.

    - (선택사항, 더 어려움) 부분 순열이 전이적임을 [subseq_trans]
      증명하시오.  즉 [l1]이 [l2]의 부분 순열이고 [l2]가 [l3]의 부분
      순열이면 [l1]은 [l3]의 부분 순열이다. 힌트: 주의깊게 귀납법을
      선택하시오! *)

(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 두 개, 선택사항 (R_provability2)  *)
(** 콕으로 아래와 같이 정의한다고 가정하자.

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

    다음 명제들 중 어느 것을 증명할 수 있는가?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(** [] *)


(* ################################################################# *)
(** * 사례 연구: 정규식 *)

(** [ev] 성질은 귀납적 정의와 이 정의에 대한 기본적인 추론 기법을
    설명하는 간단한 예를 제공하지만 매우 흥미로운 것은 아니었다. 결국
    이전에 보았던 귀납 방식이 아닌 두 가지 방식으로 정의한 짝수에 대한
    정의와 동치이고 이 두 가지 방식에 비해 귀납적 방식이 어떤 구체적인
    혜택을 제공하는 것으로 보이지는 않는다. 귀납적 정의의 표현력을 더
    잘 보여주기 위해서 컴퓨터 과학에서 고전적 개념 _정규식_을
    모델하는데 귀납적 정의를 사용하는 방법을 이제 보여준다. *)

(** 정규식은 문자열을 기술하기 위한 간단한 언어이다. 다음과 같이
    정의한다. *)

Inductive reg_exp (T : Type) : Type :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T -> reg_exp T
| App : reg_exp T -> reg_exp T -> reg_exp T
| Union : reg_exp T -> reg_exp T -> reg_exp T
| Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** 이 정의는 _다형성_을 지닌다는 점을 참고하시오. [reg_exp T]의
    정규식은 [T] 타입([T] 타입의 원소들로 이루어진 리스트들)의
    문자들로 구성하는 문자열을 기술한다.

    (보통 [T] 타입은 유한한 원소로 구성되어 있도록 가정하나 그러한
    가정을 요구하지 않는다. 이러한 점은 일반적인 관행과 약간 다르다.)
    *)

(** 다음 규칙에 따라 정규식과 문자열을 연결한다. 이 규칙은 정규식이
    어떤 문자열에 _매치_하는가를 정의한다.

      - 식 [EmptySet]은 어느 문자열에도 매치하지 않는다.

      - 식 [EmptyStr]는 빈 문자열 [[]]에 매치한다.

      - 식 [Char x]는 한 문자로 된 문자열 [[x]]에 매치한다.

      - [re1]이 [s1]에 매치하고 [re2]가 [s2]에 매치하면 [App re1 re2]는 
        [s1 ++ s2]에 매치한다.

      - [re1]과 [re2] 중 적어도 어느 하나가 [s]에 매치하면 [Union re1 re2]는
        [s]에 매치한다.   

      - 마지막으로 어떤 문자열 [s]를 [s = s_1 ++ ... ++ s_k] 문자열의 순열을
        붙인 것이고 [re]는 [s_i] 문자열들 각각에 매치하면 [Star re]는 [s]에 
        매치한다.

        특별한 경우로 문자열들의 순열은 비어 있을 수 있다. 따라서 [Star re]는 
        [re]가 무엇이든지 상관없이 빈 문자열 [[]]을 항상 매치한다.

    이렇게 서술한 정의를 [Inductive] 정의로 다음과 같이 쉽게 변환할 수 있다.  *)

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

(** 다시 반복하면, 가독성을 높이기 위해 추론 규칙 표기법을 사용하여 이
    정의를 표시할 수도 있다. 동시에 더 읽기 편한 중위 표기법을
    도입하자. *)

Notation "s =~ re" := (exp_match s re) (at level 80).

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

(** 이 규칙들은 앞에서 서술된 규칙들과 _그다지_ 동일하지는 않다는 점을
    주목하라. 우선 아무런 문자열과 매치하지 않는 [EmptySet] 규칙을
    명시적으로 포함시킬 필요는 없다.  왜냐하면 어떤 문자열 매칭
    [EmptySet]의 효과를 가질 수 있는 어떠한 규칙도 포함시키지 않기
    때문이다. (정말로 귀납적 정의의 구문으로 그러한 "부정적 규칙"을
    허용하지 조차 않는다.)

    둘째, [Union]과 [Star]에 대해 서술한 규칙들은 다음의 두 생성자에
    각각 대응한다. [MUnionL] / [MUnionR]과 [MStar0] / [MStarApp] 그
    결과 원래 규칙과 논리적으로 동치이지만 콕에서 사용하기 더
    편리하다.  왜냐하면 [exp_match]이 재귀적으로 나타난 곳들은 이
    생성자들의 직접적인 인자로 주어질 수 있기 때문이다. 이로 인해
    증거에 대한 귀납법을 적용하기 더 쉬워진다. (아래의
    [exp_match_ex1]과 [exp_match_ex2] 연습문제들에서 귀납적 선언으로
    주어진 생성자들과 서술한 규칙들을 문자 그대로 변환해놓은 귀납적
    정의에서 주어질 수 있는 생성자들이 정말로 동일하다는 것을
    증명해본다.)

    두세 가지 예제들을 가지고 이 규칙들을 설명해보자.  *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(** (마지막 예제에서 [MApp]를 문자열 [[1]]과 [[2]]에 어떻게 바로
    적용하는지 주목하시오. 증명 목적에 [[1] ++ [2]] 대신 [[1; 2]]이
    나타나 있기 때문에 콕은 이 문자열을 어떻게 분리할지 스스로 알지
    못할 것이다.)

    [inversion]을 사용하여 어떤 문자열이 주어진 정규식에 매치되지
    _않는지_도 보여줄 수 있다. *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** 도움 함수들을 정의해서 정규식을 작성하는 것을 도와줄 수
    있다. [reg_exp_of_list] 함수는 인자로 받은 리스트를 정확히
    매치하는 정규식을 만든다. *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** [exp_match]에 대한 일반적인 사실들을 증명할 수도 있다. 예를 들어,
    다음 보조 정리는 [re]에 매치하는 모든 문자열 [s]는 [Star re]에도
    매치함을 보여준다. *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(** ([app_nil_r]을 사용해서 이 정리의 목적을 [MStarApp]에서 기대하는
    것과 정확히 동일한 형태로 변경하는 것에 주목하시오.) *)

(** **** 연습문제: 별 세 개 (exp_match_ex1)  *)
(** 다음 보조 정리는 이 장의 처음 부분에서 서술한 매칭 규칙들은
    형식적인 귀납적 정의로부터 얻을 수 있음을 보인다.  *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  (* 여기를 채우시오 *) Admitted.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  (* 여기를 채우시오 *) Admitted.

(** 다음 보조 정리는 [Poly] 장의 [fold] 함수에 관하여 서술되어 있다.
    만일 [ss : list (list T)]가 문자열들의 순열 [s1, ..., sn]을
    표현한다면 [fold app ss []]는 그 문자열들 모두 함께 붙인 결과이다. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 네 개 (reg_exp_of_list)  *)
(** [reg_exp_of_list]는 다음 명세를 만족함을 보이시오. *)


Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** [exp_match]는 재귀적 구조이기 때문에 정규식 관련 증명들은 증명에
    대한 귀납적 방법을 빈번하게 요구할 것으로 기대할 수 있다. 예를
    들어 다음의 직관적인 결과를 증명하고 싶다고 가정하자. 정규식
    [re]가 어떤 문자열 [s]에 매치하면 [s]의 모든 원소들은 [re]에
    반드시 나타나야 한다. 이 정리를 기술하기 위해서 [re_chars] 함수를
    먼저 정의한다. 이 함수는 정규식에 나타난 모든 문자들을 나열한다.
 *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** 그런 다음 우리의 정리를 다음과 같이 다시 작성할 수 있다. *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [
        |x'
        |s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
        |re|s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* 수업에서 다루었음 *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite in_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite in_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite in_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.

(** [MStarApp] 경우가 흥미롭다. _두_ 귀납적 가정들을 얻는데, 하나는
    [x]가 [s1] ([re]에 매치하는)에 나타날 때 적용하고, 두 번째는 [x]가
    [s2] ([Star re]에 매치하는)에 나타날 때 적용한다. 이 것은 [re]에
    반대로 [exp_match]의 증거에 대한 귀납법이 왜 필요한지 보여주는
    좋은 사례이다.  왜냐하면 [re]는 [re]에 매치하는 문자열에 대한
    귀납적 가정을 제공할 뿐인데 [In x s2] 경우에 대해 추론할 수 없기
    때문이다. *)

  - (* MStarApp *)
    simpl. rewrite in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** 연습문제: 별 네 개 (re_not_empty)  *)
(** 재귀 함수 [re_not_empty]를 작성하여 재귀식이 어떤 문자열에
    매치하는지 테스트하시오. 이 함수가 올바르다는 사실을
    증명하시오. *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool
  (* 이 줄을 당신의 정의로 대체하시오 *). Admitted.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** [remember] 전술 *)

(** [induction] 전술에서 잠재적으로 혼동스러운 한가지 특징은 충분히
    일반적이지 않은 식에 대해 귀납법을 적용하도록 설정하기 쉽다는
    것이다. 이렇게 설정되면 ([destruct] 전술이 그러한 것 만큼) 정보를
    잃고, 증명을 완성할 수 없는 상태가 된다. 여기 예가 있다. *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** [H1]에 대해 [inversion]을 적용하면 재귀 경우들에서 그 다지
    진전하지 못한다.  그래서 귀납법이 필요하다. 첫 번째로 평범하게
    시도해본다. *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** 하지만 이제 [exp_match] 정의에서 나온 일곱가지 경우들로 얻지만
    [H1]의 가장 중요한 정보, [s1]은 [Sar re] 형태의 어떤 것에
    매치되었다는 사실을 잃어버렸다. 이로 인해 일곱 개중 두
    개([MStar0]와 [MStarApp])를 제외한 나머지 경우들은 모순이지만 이
    정의의 _모든_ 일곱가지 생성자들에 대해 증명해야한다. [MEmpty]...와
    같은 두세 가지 생성자들에 대한 증명을 여전히 진행할 수 있다. *)

  - (* MEmpty *)
    simpl. intros H. apply H.

(** ... 하지만 대부분의 경우 증명이 막힌다. [MChar]의 경우를 예로
    살펴보면 다음을 보여여 한다.

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    하지만 이를 증명하는 것은 명백히 불가능하다. *)

  - (* MChar. 막힘... *)
Abort.

(** 문제는 [Prop] 가정에 대한 [induction]은 완전히 일반적인 가정들에
    대해서는 적절히 동작한다. 즉, 모든 인자가 변수인 가정들에 대해서
    적용하기 적절하지만 [Star re]와 같이 더 복잡한 식에 대해서는
    그렇지 않다.

    (이러한 점에서 증거에 대한 [induction]은 [inversion] 보다
    [destruct]와 더 비슷하게 동작한다.)

    문제를 일으키는 식들을 명시적인 등식을 가지고 일반화시켜서 이
    문제를 해결할 수 있다.  *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  s1 =~ re' ->
  re' = Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** 증거에 대한 귀납법을 이제 직접 수행할 수 있다. 왜냐하면 첫번째
    가정의 인자가 충분히 일반적이므로 [re' = Star re] 등식을 이
    문맥에서 뒤집음으로써 대부분의 경우들을 없앨 수 있기 때문이다.

    이 증명 방법은 매우 흔해서 그러한 등식을 자동으로 생성해서 정리에
    있는 문장을 수정하지 않아도 되는 편리한 전술을 콕에서 제공한다. *)

(** [remember e as x] 전술을 사용하면 콕 시스템은 (1) 식 [e]가 나타난
    것을 모두 변수 [x]로 바꾸고, (2) 현재 문맥에 등식 [x = e]를
    추가한다.  위 결과를 보이기 위해 이 전술을 사용하는 법이 여기
    있다. *)
Abort.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** 이제 [Heqre' : re' = Star re] 이다. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** [Heqre']은 대부분의 경우에 모순이므로 즉시 결론을 내릴 수 있게
    해준다. *)

  - (* MEmpty *)  inversion Heqre'.
  - (* MChar *)   inversion Heqre'.
  - (* MApp *)    inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.

(** [Star]에 대응하는 경우들이 흥미롭다. [MStarApp] 경우에 대한 귀납적
    가정 [IH2]는 [Star re'' = Star re'] 전제를 추가로 언급하는데
    [remember]로 생성된 등식으로 부터 만들어진 것이다. *)

  - (* MStar0 *)
    inversion Heqre'. intros s H. apply H.

  - (* MStarApp *)
    inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

(** **** 연습문제: 별 네 개 (exp_match_ex2)  *)

(** 아래의 [MStar''] 보조 정리는 (그 역과 조합하면 위의 [MStar']
    연습문제) [Star]에 대한 [exp_match] 정의가 앞서 주어진 서술형
    규칙과 동일함을 보인다. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** **** 연습문제: 별 다섯개 , 고급 (pumping)  *)
(** 정규식 이론에서 첫번째 정말로 흥미로운 정리들 중 하나는 _펌핑 보조
    정리_라 부르는 것이다.  이 보조 정리에 의하면, 어떤 충분히 긴
    문자열 [s]가 정규식 [re]에 매치된다고 할때 이 문자열은 [s]의 어떤
    중간 부분을 임의의 횟수로 반복해서 "펌프"하여 [re]에 매치되는
    새로운 문자열을 만들 수 있다.

    우선 "충분히 긴"이라는 표현을 정의할 필요가 있다. 건설적 논리를
    다루고 있으므로 각 정규식 [re]에 대해 "펌프 가능성"을 보장하는
    문자열들 [s]의 최소 길이를 실제로 계산할 수 있어야 한다. *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

(** 다음으로 어떤 숫자 만큼 반복해서 문자열을 스스로에 붙이는 보조
    함수를 정의하는 것이 유용하다. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

(** 이제 펌핑 보조 정리는, 만일 [s =~ re]이고 [s]의 길이가 [re]의 최소
    펌핑 상수이라면 [s]는 세 개의 부분 문자열들로 분리하여 [s1 ++ s2
    ++ s3]로 나타낼 수 있다. [s2]는 어떤 숫자만큼 반복할 수 있고 그
    결과를 [s1]과 [s3]와 조합하면 [re]에 여전히 매치된다. [s2]는 빈
    문자열이 아니라는 것도 보장되기 때문에 이 보조 정리는 [re]에
    매치되는 원하는 길이의 문자열을 생성하는 (건설적!) 방법이 된다. *)

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** 당신이 작성할 증명을 능률적으로 하기 위해 [omega] 전술을 사용하면
    여러 곳에서 자연수에 대한 등식 또는 부등식 관련한 번거롭고
    지나치게 상세한 주장을 자동으로 완성하는데 도움이 된다. [omega]
    전술을 사용하려면 다음과 같은 [Require] 명령을 사용해야 한다.
    나중에 [omega] 전술을 설명할 것이다. 하지만 당분간 원할 때마다
    자유롭게 이 전술을 적용해도 된다. 귀납 증명의 첫 번째 경우는 이
    전술을 사용하는 예이다. *)

Require Import Coq.omega.Omega.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  (* 여기를 채우시오 *) Admitted.

End Pumping.
(** [] *)

(* ################################################################# *)
(** * 사례 연구: 반사를 개선하기  *)

(** 부울 계산과 [Prop] 문장을 종종 연관시킬 필요가 있는 것을 [Logic]
    장에서 보았다. 거기에서 했던 방식으로 둘 사이를 서로 변환하면
    번거로운 형태의 증명이 될 수 있다. 다음 정리를 증명하는 것을
    고려하자. *)

Theorem filter_not_empty_In : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_nat n m) eqn:H.
    + (* beq_nat n m = true *)
      intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** [destruct] 다음의 첫번째 분기에서 [beq_nat_true_iff] 보조 정리를
    [beq_nat n m]을 분해해서 만든 등식에 명시적으로 적용하여 [beq_nat
    n m = true] 가정을 [n = m] 가정으로 변환한다. 그런 다음 이 가정을
    사용하여 [rewrite]하여 이 경우를 증명했었다.

    [beq_nat n m]에 대해 더 나은 경우 별 분석 원리를 가능하게 하는
    귀납적 명제를 정의해서 위 과정을 간소화시킬 수 있다. 일반적으로
    직접적으로 유용하지 않은 [beq_nat n m = true]와 같은 등식을
    생성하는 대신 이 원리를 통해 우리가 정말로 필요로 하는 가정 [n =
    m]을 곧바로 제공한다.

    사실 조금 더 일반적인 것을 정의해서 단지 등식 뿐만 아니라 임의의
    성질에 대해 사용할 수 있도록 한다.  *)

Module FirstTry.

Inductive reflect : Prop -> bool -> Prop :=
| ReflectT : forall (P:Prop), P -> reflect P true
| ReflectF : forall (P:Prop), ~ P -> reflect P false.

(** 위 내용을 설명하기 전에 조금 재배치하자. [ReflectT]와 [ReflectF]
    둘다 타입이 [forall (P:Prop)]로 시작하기 때문에 [P]를 전체 귀납적
    선언의 매개변수로 두어 조금 더 읽기 쉽고 다루기 쉽게 만들 수 있다. *)

End FirstTry.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.

(** [reflect] 성질은 명제 [P]와 부 울값 [b] 두 개의 인자를 받는다.  이
    성질의 직관적인 의미는 성질 [P]가 부울 값 [b]에 _반사되어_ 있다.
    즉, 성질 [P]는 부울 값 [b]와 동치라고 해석한다. [P]가 성립하는
    필요 충분 조건이 [b = true]이다. 이 점을 확인하기 위해 정의를 보면
    [reflect P true]가 성립하는 증거를 만드는 유일한 방법은 [P]가
    참이라는 것을 보이고 [ReflectT] 생성자를 사용하는 점을 주목해야
    한다. 이 문장을 뒤집어 보면, [reflect P true] 증명으로부터 [P]에
    대한 증거를 추출하는 것이 가능해야 한다. 역으로 [reflect P
    false]를 보이는 유일한 방법은 [~ P]에 대한 증거와 [RefelctF]
    생성자를 조합하는 것이다.

    이러한 직관적인 사실을 형식화하고 두 문장이 정말로 동치라는 것을
    보이기 쉽다. *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* 수업에서 다루었음 *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

(** **** 연습문제: 별 두 개, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** "if and only if" 연결자를 사용하는 것과 비교해서 [reflect]의
    장점은 [reflect P b] 형태의 가정이나 보조 정리를 분해하면서 [b]에
    대한 경우 별 부석을 수행하고 동시에 양 갈래에 적절한 가정을 생성할
    수 있다 (첫 번째 부분 목적에는 [P]를 두 번째 부분 목적에는 [~ P]). *)

Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

(** 이번에는 [filter_not_empty_In]을 다음과 같이 새로 증명한다.
    [destruct]와 [apply]를 적용하는 것을 [destruct] 하나로 조합한 것을
    살펴보시오.  *)

(** (분명하게 이 점을 보기 위해서 콕으로 [filter_not_empty_In]을
    증명한 두 가지 방법을 자세히 보고 [destruct]의 첫 번째 경우의 도입
    부분의 증명 상태가 어떻게 다른지 관찰하시오.)  *)

Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_natP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** 연습문제: 별 세 개, 추천 (beq_natP_practice)  *)
(** 다음을 증명하기 위해 위와 같이 [beq_natP]를 사용하시오. *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if beq_nat n m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  (* 여기를 채우시오 *) Admitted.
(** [] *)

(** 이 기법은 여기서 본 증명의 경우 약간 편할 뿐이지만 일관되게
    [reflect]를 사용하면 종종 커다란 증명일 수록 눈에 띄게 더 짧고
    명확하게 증명을 작성하도록 만든다. 나중에 더 많은 예를 만나게 될
    것이다.

    [reflect] 성질을 사용하는 것은 콕 라이브러리 _SSReflect_로
    유명해졌다.  이 라이브러리는 4색 정리와 Feit-Thompson 정리와 같은
    수학에서 중요한 결과를 형식화하는데 사용되었다. 이름 SSReflect는
    _small-scale reflection_를 나타내는데, 부울 계산으로 작은 증명
    단계들을 간단하게 만드는 반사를 널리 사용하는 것을 의도한다. *)

(* ################################################################# *)
(** * 추가 연습문제 *)

(** **** 연습문제: 별 세 개, 추천 (nostutter)  *)
(** 성질을 귀납적 정의로 공식화하는 것은 이 강의에서 필요한 중요한
    능력이다. 어떠한 도움없이 이 연습문제를 해결해보라.

    리스트에 동일한 원소가 연속으로 배치되어 있으면 "말을 더듬는다"고
    하자.  "[nostutter mylist]"는 [mylist]가 말을 더듬지 않는다는
    성질이다. [nostutter]의 귀납적 정의를 만드시오. (위 연습문제의
    [NoDup] 성질과 다르다. 왜냐하면 [1;4;1]은 반복하지만 말을 더듬지는
    않는다.) *)

Inductive nostutter {X:Type} : list X -> Prop :=
 (* 여기를 채우시오 *)
.
(** 아래의 테스트들을 모두 통과하도록 확인하되 주석 처리된 제안한
    증명이 동작하지 않으면 자유롭게 변경하시오. 당신이 만든 정의가
    저자가 만든 것과 다르지만 정확할 수 있다. 그러한 경우 이 예제들을
    증명할 때 다른 증명이 필요할 수도 있다. (제안한 증명에 아직
    설명하지 않은 많은 전술들을 상용하고 있음을 주목해야 할 것이다.
    이 전술들을 사용하여 [nostutter]를 정의한 다른 가능한 방법들에
    대해서도 적용될 수 있도록 더 강건한 증명을 만들 수 있다.  당연히
    주석을 해제하고 제안한 증명을 그대로 이용할 수 있지만 더 기본적인
    전술을 사용해서 증명할 수도 있다.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
(* 여기를 채우시오 *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_2:  nostutter (@nil nat).
(* 여기를 채우시오 *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_3:  nostutter [5].
(* 여기를 채우시오 *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* 여기를 채우시오 *) Admitted.
(* 
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** 연습문제: 별 네 개, 고급 (filter_challenge)  *)
(** [Poly] 장의 [filter] 정의가 추상적 명세에 일치하는 것을 증명하자.
    여기 영어로 비형식적으로 작성한 명세가 있다:

    리스트 [l]은 만일 리스트가 [l1]과 [l2]와 모두 동일한 원소들을
    포함하고, [l1]과 [l2]의 순서를 유지하되, 서로 중간에 끼어들 수
    있다면 이 리스트는 [l1]과 [l2]의 "순차 병합"이다. 예를 들어,

    [1;4;6;2;3]

    는 아래 두 리스트의 순차 병합이다.

    [1;6;2]

    과

    [4;3].

    이제 집합 [X], 함수 [test: X->bool], [list X] 타입의 리스트 [l]을
    가정하자. 그리고 [l]은 두 리스트 [l1]과 [l2]의 순차 병합이고 [l1]의
    각 항목은 [test]를 만족하고 [l2]의 어느 항목도 이 테스트를 만족하지 
    않는다. 그렇다면, [filter test l = l1]이다.

    이 명세를 콕의 정리로 작성하고 증명하시오. (리스트가 다른 두 리스트들의
    병합이라는 것부터 정의해야 할 것이다. 귀납적 관계로 정의하되 [Fixpoint]를
    사용하지 마시오.) *)

(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 다섯개 , 고급, 선택사항 (filter_challenge_2)  *)
(** [filter]의 동작 특성을 이렇게 다르게 정의할 수 있다. [test]가
    [true]로 판정을 내리는 성질을 갖는 [l]의 모든 부분 순열들 중에
    [filter test l]은 가장 긴 순열이다. 이 주장을 콕으로 작성해서
    증명하시오. *)

(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 네 개, 선택사항 (palindromes)  *)
(** 팰린드롬은 뒤로 읽어도 앞으로 읽는 것과 동일한 순열이다.

    - [list X]에 대한 귀납적 명제 [pal]을 정의해서 팰린드롬이 의도하는
      바를 정확히 기술하시오. (힌트: 세가지 경우가 필요하다. 리스트 구조에 
      관하여 정의해야 한다. 왜냐하면 다음과 같이 생성자 하나만 두면,

        c : forall l, l = rev l -> pal l

      당연해보이지만 그다지 쉽게 증명하지 못할 것이다.)

    - 다음 명제 ([pal_app_rev])을 증명하시오.

       forall l, pal (l ++ rev l).

    - 다음 명제 ([pal_rev])을 증명하시오.

       forall l, pal l -> l = rev l.  *)

(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 다섯개 , 선택사항 (palindrome_converse)  *)
(** 다시 한번, 역 방향을 증명하기는 증거가 부족하기 때문에 훨씬 더 어렵다.
    이전 연습문제의 [pal] 정의를 사용하여 다음을 증명하시오.

     forall l, l = rev l -> pal l.  *)

(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 네 개, 고급, 선택사항 (NoDup)  *)
(** [Logic] 장에서 [In] 성질의 정의를 다시 기억해보자. 이 성질은 list
    [l]에서 적어도 한 번 [x] 값이 나타난다고 주장한다.  *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** 첫번째 작업은 [In]을 사용해서 [disjoint X l1 l2] 명제를 정의하는
    것이다.  이 명제는 [l1]과 [l2]가 공통 원소가 없는 (타입 X의 원소를
    갖는) 리스트일 때 바로 증명가능해야 한다. *)

(* 여기를 채우시오 *)

(** 다음 작업은 [In]을 사용하여 귀납적 명제 [NoDup X l]을 정의한다.
    [l]의 모든 원소가 다른 원소와 다른 (타입 X의 원소를 갖는)
    리스트이면 바로 증명 가능해야 한다. 예를 들어, [NoDup nat
    [1;2;3;4]]와 [NoDup bool []]은 증명 가능하고 [NoDup nat [1;2;1]]과
    [NoDup bool [true;true]]는 증명할 수 없어야 한다.  *)

(* 여기를 채우시오 *)

(** 마지막으로 [disjoint], [NoDup], [++] (리스트 붙이기)를 연관짓는 한
    가지 또는 그 이상 흥미로운 정리들을 기술하고 증명하시오.  *)

(* 여기를 채우시오 *)
(** [] *)

(** **** 연습문제: 별 네 개, 고급, 선택사항 (pigeonhole principle)  *)
(** _비둘기 집 원리_는 세는 것에 대한 기본적인 사실을 기술한다.  만일
    [n]개 이상의 항목들을 [n]개의 비둘기 집에 분배하면 어떤 비둘기
    집은 반드시 적어도 둘 이상의 항목을 포함해야 한다. 종종
    그러하듯이, 숫자에 관한 이 명백하고 당연한 사실을 증명하려면
    사소하지 않은 절차가 필요하다. 이제 충분히 갖췄다... *)

(** 먼저 쉽고 유용한 보조 정리를 증명하시오.  *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  (* 여기를 채우시오 *) Admitted.

(** 이제 [repeats] 성질을 정의하되, [repeats X l]은 [l]이 적어도 하나
    반복되는 ([X] 타입의) 원소를 포함하는 주장이다.  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* 여기를 채우시오 *)
.

(** 자, 비둘기 집 원리를 형식화하는 방법이 여기 있다. 리스트 [l2]는
    비둘기 집 표시들의 리스트이고, 리스트 [l1]은 항목들 리스트를
    할당한 라벨들을 표현한다. 만일 라벨보다 많은 항목이 있다면 적어도
    두 항목은 동일한 라벨을 가져야 한다. 즉 list [l1]은 반복되는
    원소를 포함한다.

    [excluded_middle] 가정을 사용해서 [In]이 결정가능함을 보이면 (즉,
    [forall x l, (In x l) \/ ~ (In x l)]) 더 쉽게 증명할 수 있다.
    하지만 [In]이 결저가능하다고 _가정하지 않고도_ 증명을 진행할 수도
    있다. 이렇게 증명을 해낸다면 [excluded_middle] 가정을 필요로 하지
    않을 것이다. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
  (* 여기를 채우시오 *) Admitted.
(** [] *)


(** $Date: 2016-12-17 23:53:20 -0500 (Sat, 17 Dec 2016) $ *)
