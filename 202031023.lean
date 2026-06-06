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





-/
