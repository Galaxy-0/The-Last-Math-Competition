# Solution Review — Conjecture 00000000261 (PR 443)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004103517`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added
- [x] Full LaTeX source and PDF read; independent PDF build passed
- [x] Self-contained Lean project independently built
- [x] Direct warning-as-error Lean check passed
- [x] Auxiliary Python program run and independently checked
- [x] No incomplete proof, native decision shortcut, custom axiom, unsafe implementation, or external binding
- [x] Axioms are only `propext` and/or `Quot.sound`

## Counterexample

The official claim says that for every fundamental discriminant \(d\equiv1\pmod4\), the coefficient \(u\) of the fundamental Pell solution never divides \(t\). Take \(d=5\).

- Under the full unit/norm-\(\pm1\) convention, the fundamental pair is \((t,u)=(1,1)\), corresponding to \((1+\sqrt5)/2\). It satisfies \(1^2-5\cdot1^2=-4\), and is the unique positive pair minimizing the algebraic value. Here \(u=1\mid t=1\).
- Under a norm-\(+1\) convention, the fundamental pair is \((3,1)\), corresponding to \((3+\sqrt5)/2\). It satisfies \(3^2-5\cdot1^2=4\), and is uniquely minimal. Here \(u=1\mid t=3\).

Thus the universal printed assertion \(u\nmid t\) is false. The submission correctly states that this is not a claim about the different conventional AAC condition \(p\nmid u\).

## Formal verification

Lean defines fundamental discriminants, both relevant Pell conventions, exact algebraic-value ordering without floating point, and fundamentality by minimality against every positive candidate. It proves squarefreeness of 5, both witness equations, unbounded coordinatewise minimality, uniqueness, divisibility, and negation of the official universal statement.

Independent `lake build`, direct warning-as-error Lean, LaTeX, and the supplementary exact Python check all passed. Principal theorem audits use only standard logical axioms.

## Verdict

APPROVED — correct, non-vacuous disproof of the literal Conjecture 00000000261.
