/-
- Part 1
- Scenario 1
-/
theorem scenario1 (x1 x2 y1 y2 z : Prop)
  (r1 : x1 ∨ x2)
  (r2 : y1 ∨ y2)
  (r3 : x1 → z)
  (r4 : x2 → z)
  (r5 : y1 → z)
  (r6 : y2 → z) : z := by
  cases r1  with
  | inl hx1 => exact r3 hx1
  | inr hx2 => exact r4 hx2

/-
Analysis

======== Rules applied: ========
1. Applied disjunction elimination (proof by cases) to r1 : x1 ∨ x2.
   Justification: r1 states that either x1 or x2 holds, so both cases must be considered.

2. In the first case, I obtained hx1 : x1.
   Applied implication elimination (modus ponens) using r3 : x1 → z and hx1 : x1 to derive z.

3. In the second case, I obtained hx2 : x2.
   Applied implication elimination (modus ponens) using r4 : x2 → z and hx2 : x2 to derive z.

4. Since both cases produce z, I concluded z by disjunction elimination.

======== Strategy: ========

For this scenario, I used the course-prerequisite pathway. Hypothesis r1 guarantees
that the student has passed at least one prerequisite (x1 or x2).
Hypotheses r3 and r4 state that each prerequisite is individually sufficient for eligibility.
Therefore, by performing a proof by cases on r1, either x1 or x2 can be used to derive z.
This allows the goal z to be proved without using the approval pathway represented by r2, r5, and r6.

======== Alternative strategy: ========
An alternative strategy would be to use the approval pathway with
r2, r5, and r6. Since r2 states y1 ∨ y2 and r5, r6 show either approval
implies z, this would also prove eligibility to take the advance module.

======== Hardest step: ========
The hardest step was recognising that only one independent pathway is needed.
Although six hypotheses are provided, the proof can be completed using only r1, r3, and r4.

======== Formalization assumptions: ========
I assumed x1 and x2 represent sufficient prerequisites specifically because the scenario states
the eligibility is based on "..two independent approval pathways."
I also assume z means final eligibility, and that each implication rule directly establishes
eligibility without needing both a prerequisite and an approval.
-/


/-Scenario 2-/

theorem scenario2 (a b c d : Prop) :
  ((b → d) ∧ (¬a → (c ∧ d)) ∧ (a ∨ d) ∧ b ∧ ¬c) → (a ∧ d) := by
  intro h
  rcases h with ⟨hbd, hnad, had, hb, hnc⟩

  have hd : d := hbd hb

  have ha : a := by
    by_cases ha : a
    · exact ha
    · have hcd : c ∧ d := hnad ha
      have hc : c := hcd.left
      exact False.elim (hnc hc)

  exact And.intro ha hd
/-
Analysis

======== Rules applied: ========
1. I assumed the banking security conditions : (b → d) ∧ (¬a → (c ∧ d)) ∧ (a ∨ d) ∧ b ∧ ¬c
these premises are provided by the scenario and form the basis from which the conclusion (a ∧ d) must be derived.

2. I applied conjunction elimination by decomposing h into hbd, hnad, had, hb, and hnc.
In other words, the premise is a nested set of rules containing individual banking rules and facts.

3. I applied implication elimination (modus ponens) using hbd : b → d and hb : b.
Since the transaction exceeds typical spending and the security policy states that such transactions
require biometric verification, therefor d is expected.

4. Considered the possibility that the device is unregistered (¬a). Using ¬a → (c ∧ d), I derived c ∧ d and therefore c.
Since ¬c is also given, this results in both c and ¬c being true simultaneously, which is a contradiction.

5. Since the assumption ¬a leads to contradiction, I concluded that the device must be registered (a).

6. Applied conjunction introduction to combine a and d into the final conclusion a ∧ d.


======== Strategy: ========

The goal is a conjunction, a ∧ d, so I first proved each component separately.
The proof of d is direct: hbd : b → d and hb : b give d by modus ponens.
The proof of a is indirect: assuming the device is unregistered would force c ∧ d, and therefore c,
but this contradicts the given ¬c. Therefore the device must be registered.

======== Alternative strategy: ========

An alternative strategy would be to use the premise had : a ∨ d and perform proof by cases. However,
this is less direct because a ∨ d only says that one of a or d holds, not that both hold. So that path is complicated.
I chose not to use it because d follows directly from b → d and b, while 'a' follows from the contradiction
between ¬a → (c ∧ d) and ¬c.

======== Hardest step: ========

The hardest step was proving 'a' because there is no direct hypothesis stating that the device is registered.
The key logical insight is that the unregistered device case is incompatible with the evidence: if ¬a were true,
the system rule would require c however the premises state ¬c. Therefore, the only consistent possibility is that 'a' holds.

======== Formalization assumptions: ========

I assume that a, b, c, and d describe the current transaction state. I interpret ¬a as the device being unregistered,
and ¬c as the location history being inconsistent. I also assume that the implication ¬a → (c ∧ d) is a strict requirement:
if the device is unregistered, then both location consistency and biometric verification must apply.
Under these assumptions, the inconsistency of the location should rule out the unregistered device case.
-/

/- ############# Scenario 3 ############### -/

/-

1. Choose ONE formalisation (α or β). State which and justify in 2–3 sentences.

I choose formalisation β: (p ∧ q) → ¬r. Because this better aligns with the safety-monitoring interpretation of Rule A, because the word “check”
can mean that the system verfies whether a person is present and finds that no person is present. This also fits consistently
with Rule C, which states that motion was detected and the oven is on, but no person is present.

-/

/-
2. Write the theorem signature under YOUR chosen formalisation. Prove it in Lean.
-/
theorem scenario3_beta (p q r s : Prop)
  (ruleA : (p ∧ q) → ¬r)
  (ruleB : (q ∧ ¬r) → s)
  (ruleC : p ∧ q ∧ ¬r) : s := by
  have hp : p := ruleC.left
  have hq : q := ruleC.right.left
  have hpq : p ∧ q := And.intro hp hq
  have hnr : ¬r := ruleA hpq
  have hqnr : q ∧ ¬r := And.intro hq hnr
  exact ruleB hqnr

  /-
======== Rules applied for β: ========

1. Conjunction elimination: to ruleC : p ∧ q ∧ ¬r.
   ruleC contains the facts p, q, and ¬r, so I first extracted p and q.

2. Conjunction introduction: to hp : p and hq : q to derive hpq : p ∧ q.
   Rule A β requires p ∧ q as its input.

3. Implication elimination: modus ponens using ruleA : (p ∧ q) → ¬r and hpq : p ∧ q to derive hnr : ¬r.
   Under β, motion and oven-on imply that no person is confirmed.

4. Conjunction introduction: to hq : q and hnr : ¬r to derive hqnr : q ∧ ¬r.
   Rule B requires q ∧ ¬r as its input.

5. Implication elimination: modus ponens using ruleB : (q ∧ ¬r) → s and hqnr : q ∧ ¬r to derive s
   Since the oven is on and no person is confirmed, the shutdown is triggered
-/

/-
3. Write the theorem signature under the OTHER formalisation. Prove it in Lean. Submit BOTH working proofs. For both proofs, list the rules applied in each proof step.
-/
theorem scenario3_alpha (p q r s : Prop)
  (ruleA : (p ∧ q) → r)
  (ruleB : (q ∧ ¬r) → s)
  (ruleC : p ∧ q ∧ ¬r) : s := by
  have hp : p := ruleC.left
  have hq : q := ruleC.right.left
  have hnr : ¬r := ruleC.right.right
  have hpq : p ∧ q := And.intro hp hq
  have hr : r := ruleA hpq
  have contradiction : False := hnr hr
  exact False.elim contradiction

  /-
======== Rules applied for α: ========

1. Conjunction elimination to ruleC : p ∧ q ∧ ¬r.
   ruleC contains the facts p, q, and ¬r, so I extracted each component.

2. Conjunction introduction to hp : p and hq : q to derive hpq : p ∧ q.
   Rule A α requires p ∧ q as its input.

3. Implication elimination: modus ponens using ruleA : (p ∧ q) → r and hpq : p ∧ q to derive hr : r.
   under α, motion and oven-on imply that a person is confirmed present.

4. Negation elimination: using hnr : ¬r and hr : r to derive contradiction : False.
   ruleC states that no person is confirmed, while Rule A α derives that a person is confirmed. These cannot both hold.

5. False elimination: to derive s from contradiction.
   Once the assumptions are inconsistent, any proposition follows, including shutdown s.
-/

/-
4. Line-by-line comparison: number each line of both proofs. For every line that differs, state the line number and explain in one sentence what is different and why (which logical principle causes the divergence).

======== Line differences  (BE CAREFUL WHEN EDITING TEXT ABOVE - LINES WILL SHIFT)========

- β 144 vs α 177:
In β, line 144 constructs hpq : p ∧ q, while in α, line 177 extracts hnr : ¬r from ruleC.
This difference occurs because the β proof uses Rule A to derive ¬r, while the α proof needs ¬r from Rule C to later form a contradiction.

- β 145 vs α 178:
In β, line 145 applies Rule A β to derive hnr : ¬r, while in α, line 178 constructs hpq : p ∧ q.
This reflects the different meaning of Rule A: β derives absence of a confirmed person, while α requires p ∧ q to derive presence of a confirmed person

- β 146 vs α 179:
In β, line 146 constructs hqnr : q ∧ ¬r, while in α, line 179 derives hr : r from Rule A α.
The divergence occurs because β proceeds toward Rule B normally, while α produces r, which conflicts with ¬r.

- β 147 vs α 180:
In β, line 147 applies Rule B to derive s from q ∧ ¬r, while in α, line 180 derives False from hnr : ¬r and hr : r.
The logical divergence is that β uses modus ponens with Rule B, while α uses contradiction.

- α 181:
The α proof needs False elimination to derive s from contradiction, while the β proof already derived s directly from Rule B.
This shows that α proves shutdown only through inconsistency, whereas β proves shutdown through the intended safety rule.

-/

/-

5. Domain reflection (3–4 sentences): which formalisation better captures the homeowner’s intent? Reference the specific word in Rule A that creates the ambiguity and explain its two possible readings, connecting to Unit 1 Lesson 3.

I believe formalisation β better captures the homeowner’s intent. The ambiguity comes from the word “check” in Rule A.
One interpretation (α) is that checking guarantees a person is confirmed present, leading to (p ∧ q) → r. A second interpretation (β) is that
checking determines whether a person is present and may find that no person is confirmed, leading to (p ∧ q) → ¬r.
This reflects the idea from Unit 1 Lesson 3 that natural language is often ambiguous and that different logical representations
can be derived from the same statement depending on how key terms are interpreted.
-/

/- ########################################## -/
/- ############## Scenario 4 ################ -/
/- # Autonomous Vehicle Collision Avoidance # -/
/- ########################################## -/

/-
Use case: An autonomous vehicle receives input from its perception system.
If either an obstacle or pedestrian is detected, the system confirms a collision risk.
Once collision risk is confirmed, the emergency braking system is activated.
-/

/-
1. Name your 4 propositions with English meanings (as Lean comments).

p = obstacle is detected ahead
q = pedestrian is detected ahead
r = collision risk is confirmed
s = emergency braking is activated
-/

/-
2. Write the theorem signature with named hypotheses. Prove it in Lean.
-/
theorem scenario4 (p q r s : Prop)
  (h1 : p ∨ q)
  (h2 : p → r)
  (h3 : q → r)
  (h4 : r → s) : r ∧ s := by

  have hr : r := by
    cases h1 with
    | inl hp =>
        exact h2 hp
    | inr hq =>
        exact h3 hq

  have hs : s := h4 hr

  exact And.intro hr hs

/-
3. Explanation: rules applied in order, alternative strategy, and the hardest step you faced.
-/
  /-
======== Rules applied: ========

1. Applied disjunction elimination / proof by cases to h1 : p ∨ q.
   h1 states that either an obstacle is detected ahead or a pedestrian is detected ahead, so both cases must be considered.

2. In the first case, I obtained hp : p.
   Applied implication elimination / modus ponens using h2 : p → r and hp : p to derive r.
   If an obstacle is detected, then collision risk is confirmed.

3. In the second case, I obtained hq : q.
   Applied implication elimination / modus ponens using h3 : q → r and hq : q to derive r.
   If a pedestrian is detected, then collision risk is confirmed.

4. Since both cases produce r, I concluded r by disjunction elimination.
   Regardless of whether the detected risk comes from an obstacle or a pedestrian, collision risk is confirmed.

5. Applied implication elimination / modus ponens using h4 : r → s and hr : r to derive s.
   Once collision risk is confirmed, emergency braking is activated.

6. Applied conjunction introduction using hr : r and hs : s to derive r ∧ s.
   Since both collision risk and emergency braking have been established, they can be combined into the final goal.

======== Alternative strategy: ========

An alternative strategy would be to make the goal only s instead of r ∧ s.
In that case, the proof could first derive r by proof by cases and then use h4 : r → s to derive s.
However, I chose r ∧ s as the goal because it makes the reasoning more explicit: the vehicle first
confirms collision risk and then activates emergency braking.

======== Hardest step: ========

The hardest step was designing the scenario so that it was not just a simple linear implication chain.
The proof needed to require at least two different proof rules, so I introduced h1 : p ∨ q to represent two possible
perception inputs and used proof by cases to derive r in both branches.
-/

/-
4. Design rationale (3–4 sentences): why these hypotheses model a real safety concern.
Explain why the proof structure mirrors the real-world reasoning a vehicle controller
would perform.
-/
/-

======== Design rationale: ========

These hypotheses model a realistic autonomous vehicle safety concern because collision risk can be detected through
multiple perception sources. An obstacle detected ahead or a pedestrian detected ahead are both valid reasons for
the vehicle to conclude that a collision risk exists. Once collision risk is confirmed, the vehicle's safety
controller should activate emergency braking to prevent an accident.

The proof structure mirrors the reasoning performed by a real vehicle controller. The perception system first
evaluates different possible sources of danger (obstacle or pedestrian detection) and confirms collision risk
regardless of which source triggered the alert. The controller then uses this confirmed risk assessment to
activate emergency braking, producing the final safety response.

-/

/-
5. Counterfactual analysis: choose ONE hypothesis and REMOVE it
-/

/-

======== Counterfactual analysis: ========

Removed hypothesis:

h4 : r → s

(a) Is the goal still provable?

No. The goal r ∧ s is no longer provable.

(b) Which proof step breaks?

The proof step that breaks is:

have hs : s := h4 hr

Without h4, the proof can still derive hr : r from h1, h2, and h3, but there is no rule allowing the system to derive s from r.
Therefore, the evidence for emergency braking is missing.

(c) Real-world safety consequence:

Removing h4 represents a failure in the emergency braking controller.
The perception and risk-assessment subsystems may still detect an obstacle or pedestrian and confirm collision risk,
but the vehicle no longer has a rule connecting confirmed collision risk to braking action. In real-world terms,
this means the vehicle may correctly identify danger but fail to activate emergency braking, creating a serious collision risk.

-/

/- ########################################## -/
/- ################ Part 2 ################## -/
/- ########################################## -/

opaque conj : Prop → Prop → Prop
opaque provable : Prop → Prop

axiom AxConjElimRight : ∀ x y, provable (conj x y) → provable y
axiom AxConjElimLeft  : ∀ x y, provable (conj x y) → provable x
axiom AxConjIntro     : ∀ x y, provable x → provable y → provable (conj x y)
axiom AxPrTrue        : provable True
axiom AxNotPrFalse    : provable False → False

/- EX1 -/
theorem ex1 : ∀ x, ¬ provable (conj x False) ∧ (provable x → ¬ provable False) := by
  intro x
  constructor
  · intro hConj
    have hFalse : provable False := AxConjElimRight x False hConj
    exact AxNotPrFalse hFalse
  · intro hx
    intro hFalse
    exact AxNotPrFalse hFalse

/-
TRACE for ex1

1. Introduced an arbitrary proposition x.
   This is neeeded because the theorem states ∀ x.

2. Applied conjunction introduction using constructor.
   This splits the goal into two subgoals:
   ¬ provable (conj x False)
   and:
   provable x → ¬ provable False

3. To prove ¬ provable (conj x False), I assumed hConj : provable (conj x False).
   Since negation means implication to False, proving ¬ provable (conj x False) means showing that this assumption leads to
   contradiction

4. Applied AxConjElimRight to hConj.
   This derives hFalse : provable False from provable (conj x False)

5. Applied AxNotPrFalse to hFalse.
   This turns hFalse : provable False into False, completing the contradiction.

6. To prove provable x → ¬ provable False, I assumed hx : provable x and hFalse : provable False.
   The assumption hx is not needed, because provable False is impossible independently of x.

7. Applied AxNotPrFalse to hFalse.
   This derives False and therefore proves ¬ provable False.

CONCEPT for ex1

This theorem expresses a consistency property of the abstract provability system. It says that a conjunction in the right-hand
 side is False cannot be provable, because AxConjElimRight would then make False provable. But, AxNotPrFalse states that
 provable False is impossible. The second part says that even if an arbitrary proposition x is provable, this does not allow the
 system to prove False.
-/

/- EX2 -/
theorem ex2 : ∀ x y, provable (conj x False) → provable y := by
  intro x
  intro y
  intro hConj
  have hFalse : provable False := AxConjElimRight x False hConj
  have contradiction : False := AxNotPrFalse hFalse
  exact False.elim contradiction

/-
TRACE for ex2

1. Introduced arbitrary propositions x and y.
   This is required because the theorem states ∀ x y

2. Assumed hConj : provable (conj x False).
   This is the premise of the implication

3. Applied AxConjElimRight to hConj.
   This derives hFalse : provable False from provable (conj x False).

4. Applied AxNotPrFalse to hFalse.
   This derives contradiction : False

5. Applied False.elim to contradiction.
   From False, any proposition follows, including provable y

CONCEPT for ex2

EX2 expresses the principle of explosion in the abstract provability system. If provable (conj x False) were available,
then AxConjElimRight would allow us to derive provable False. But AxNotPrFalse states that provable False leads to contradiction.
Once a contradiction is obtained, Lean can derive any goal, so provable y follows.
-/

/- EX3 -/
theorem ex3 : ∀ x y z, provable (conj x (conj y z)) → provable (conj (conj y x) z) := by
  intro x
  intro y
  intro z
  intro hxyz

  have hx : provable x := AxConjElimLeft x (conj y z) hxyz
  have hyz : provable (conj y z) := AxConjElimRight x (conj y z) hxyz
  have hy : provable y := AxConjElimLeft y z hyz
  have hz : provable z := AxConjElimRight y z hyz

  have hyx : provable (conj y x) := AxConjIntro y x hy hx
  exact AxConjIntro (conj y x) z hyx hz

/-
TRACE for ex3

1. Introduced arbitrary propositions x, y, and z.
   This is required because the theorem states ∀ x y z

2. Assumed hxyz : provable (conj x (conj y z)).
   This is the premise of the implication

3. Applied AxConjElimLeft to hxyz.
   This derives hx : provable x from provable (conj x (conj y z))

4. Applied AxConjElimRight to hxyz.
   This derives hyz : provable (conj y z) from provable (conj x (conj y z)).

5. Applied AxConjElimLeft to hyz.
   This derives hy : provable y from provable (conj y z)

6. Applied AxConjElimRight to hyz.
   This derives hz : provable z from provable (conj y z)

7. Applied AxConjIntro to hy and hx.
   This derives hyx : provable (conj y x)

8. Applied AxConjIntro to hyx and hz.
   This derives the final goal: provable (conj (conj y x) z)

CONCEPT for ex3

This theorem shows that the abstract provability system can rearrange the structure of nested conjunctions using the
conjunction elimination and introduction axioms. Starting from a proof of x combined with y and z, the proof extracts x, y, and z
individually, then rebuilds them in a different order as (y ∧ x) ∧ z. Because conj is opaque, this rearrangement is not automatic;
it is possible only through the stated axioms for eliminating and introducing conjunctions.
-/

/-
Section B1
Constructed Classical Theorem
-/

/-
Theorem Statement:

This theorem states that for any proposition x, either provable x holds or provable x does not hold.
-/

open Classical

theorem b1 : ∀ x, provable x ∨ ¬ provable x := by
  intro x
  exact em (provable x)

/-
TRACE for B1

1. Opened Classical reasoning using "open Classical"
   It allows the proof to use the law of excluded middle (em)

2. Arbitrary proposition x
   Theorem stating for ∀ x, where x is treated as an arbitrary proposition

3. Apply em to the proposition provable x
   em (provable x) gives provable x ∨ ¬ provable x

4. The goal provable x ∨ ¬ provable x follows directly from classical em


CONCEPT answering:

(a) What does the theorem mean?

 - This theorem says that for any proposition x, either x can be proved or it cannot be proved. The theorem does not tell
   which one is true for a particular x, only that one of the two possibilities must hold

(b) Where exactly does the constructive proof attempt fail?

 - A constructive proof fails at the point where we need to prove the disjunction provable
   x ∨ ¬ provable x. Constructively, proving a disjunction requires evidence for one side: either a
   proof of provable x or a proof that provable x leads to contradiction. For an arbitrary x, no such evidence
   is available

(c) Why does Classical reasoning resolve it?

 - Classical reasoning has the law of excluded middle. Applying em to provable x Lean obtains provable x ∨ ¬ provable x
   directly without need to construct evidence for one particular side

(d) What does this reveal about the difference between constructive and classical provability?

 - This shows that constructive reasoning needs explicit evidence to prove a disjunction while classical reasoning permits a
   disjunction to be accepted because one of the two alternatives must hold. In this theorem, classical logic can decide
   provable x ∨ ¬ provable x abstractly, even though the proof gives no actual method for determining which side is true.

-/

/-
Section B2
Axiom Dependency Analysis

Chosen theorem for Q1–Q4: ex3

 - ex3: ∀ x y z, provable (conj x (conj y z)) → provable (conj (conj y x) z)
-/

/-
Q1. Which axioms does the proof of ex3 actually use?

The proof of ex3 uses three axioms:

1. AxConjElimLeft
   lines: 476
   have hx : provable x := AxConjElimLeft x (conj y z) hxyz

   It is used to extract provable x from provable (conj x (conj y z)).

   Used in line: 478
   have hy : provable y := AxConjElimLeft y z hyz

   extracts provable y from provable (conj y z)

2. AxConjElimRight
   line: 477
   have hyz : provable (conj y z) := AxConjElimRight x (conj y z) hxyz

   Extracts provable (conj y z) from provable (conj x (conj y z)).

   Also used in the line: 479
   have hz : provable z := AxConjElimRight y z hyz

   Extracts provable z from provable (conj y z)

3. AxConjIntro
   line: 481
   have hyx : provable (conj y x) := AxConjIntro y x hy hx

   Builds provable (conj y x) from provable y and provable x.

   line: 482
   exact AxConjIntro (conj y x) z hyx hz

   It builds the final conclusion provable (conj (conj y x) z)
-/

/-
Q2. Choose one used axiom. Remove it hypothetically. Could the theorem still be proved?
If no: which step fails and why? If yes: sketch the alternative path.

AxConjIntro

If AxConjIntro was removed the theorem ex3 could not be proved with this proof.
The proof could still extract provable x, provable y, and provable z using AxConjElimLeft and AxConjElimRight.
However, the step : have hyx : provable (conj y x) := AxConjIntro y x hy hx
would fail because there will be no axiom allowing to build provable (conj y x) from provable y and provable x

Last step : exact AxConjIntro (conj y x) z hyx hz. would also fail for the same reason: Without AxConjIntro, the system can
decompose conjunctions but but will no longer be able to construct new conjunctions.
Therefore ex3 would not be provable using this axiom system
-/

/-
Q3. For each unused axiom: explain in one sentence why it is not needed for this specific theorem.

The unused axioms in ex3 are AxPrTrue and AxNotPrFalse.

- AxPrTrue: is not needed because the proof never requires proving True or using provable True as intermediate step

- AxNotPrFalse: is not needed because the proof never derives provable False and does not use contradiction reasoning

-/

/-
Q4. Which single axiom is most essential to your chosen theorem?
Why does removing it make the theorem fundamentally unprovable?

The most essential axiom for ex3 is AxConjIntro

The goal of ex3 is to prove: provable (conj (conj y x) z)

Without AxConjIntro, the proof could still extract provable x, provable y, and provable z using AxConjElimLeft and AxConjElimRight
 but there would be no way to combine them into the required conjunctions.
Therefore removing AxConjIntro makes the theorem unprovable
-/

/-
Q5 Hypothetical Sixth Axiom

Extended system with disjunction predicate and a new axiom:
-/

opaque disj : Prop → Prop → Prop

axiom AxDisjIntro : ∀ x y, provable x → provable (disj x y)

/-
(a) Does AxDisjIntro make any of ex1, ex2, or ex3 easier to prove? Why or why not?

 - No. AxDisjIntro does not make ex1, ex2, or ex3 easier to prove.

 - ex1, ex2, and ex3 do not mention disj. AxDisjIntro can only produce terms of the form provable (disj x y),
but the goals of ex1, ex2, and ex3 involve only provable, conj, and False.
Therefore, AxDisjIntro cannot replace any proof step in those theorems
-/

/-
(b) Could AxDisjIntro make any original axiom redundant for any specific theorem? Justify with reference to proof steps.

 - Also no. AxDisjIntro does not make any original axiom redundant for ex1, ex2, or ex3.

In ex1 and ex2, AxDisjIntro cannot derive provable False or contradiction
In ex3 AxDisjIntro cannot replace the conjunction axioms because it only introduces disjunctions
-/

/-
(c) Write one new theorem involving provable (disj...) that is only provable because both AxDisjIntro and the original five axioms work together.
-/

theorem exDisj : ∀ x y, provable (conj x y)→ provable (disj x y) :=by
  intro x
  intro y
  intro hxy
  have hx : provable x := AxConjElimLeft x y hxy
  exact AxDisjIntro x y hx

/-

Theorem: If conj x y is provable then disj x y is provable.

Proof:
1. Assume provable (conj x y)
2. Then AxConjElimLeft is used to get provable x
3. Then AxDisjIntro to get provable (disj x y)

why neither system alone suffices?:
 - Original axioms cannot prove disj because they do not mention disj
 - AxDisjIntro alone is not enough because it needs provable x as input
 - Therefore the theorem requires both AxConjElimLeft and AxDisjIntro.
-/


/-
Q6 Cross-Theorem Comparison:
 - TODO
-/
