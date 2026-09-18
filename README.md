# JSP-000301: Consecutive powerful numbers

This project formalizes a complete counterexample for JSP-000301, the question:

> If two consecutive positive integers are powerful, must at least one be a perfect square?

The theorem proves that `12167` and `12168` are consecutive powerful numbers and that neither is a perfect square.

## Attribution

The mathematical counterexample is attributed to Solomon W. Golomb. This repository contributes a Lean formalization of that existing result. It does not claim mathematical discovery.

Sources:

- [JSP-000301 catalog entry](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301)
- [Erdos Problem 365](https://www.erdosproblems.com/365)
- [Golomb, Powerful numbers](https://doi.org/10.2307/2317020)

## Formal statement

`Jsp301/Basic.lean` defines `Powerful n` as the property that every prime divisor `p` of `n` satisfies `p^2 ∣ n`. It proves:

```lean
∃ n : ℕ,
  Powerful n ∧ Powerful (n + 1) ∧
  (¬ ∃ k : ℕ, n = k ^ 2) ∧
  (¬ ∃ k : ℕ, n + 1 = k ^ 2)
```

with witness `n = 12167`.

## Reproduce

Requirements:

- Lean 4
- Lake
- Mathlib

Run:

```sh
lake update
lake build Jsp301
lake env lean Main.lean
```

The proof contains no `sorry` or `admit`.

## Scope

This project is intended as an external Lean formalization contribution for JSP-000301. Before submitting a claim, the contributor should publish this repository under their own GitHub account, create a pinned commit, and follow the Justin Sun Prize contribution and attribution requirements.
