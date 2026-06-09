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
