# Ulam(1,n) 无穷性及计数下界

## 中文证明

取整数 n ≥ 2。令 a₁=1，a₂=n。此后每一项是严格大于前一项、并能唯一表示为
两个不同的已有序列元素之和的最小整数。用较小加数在前来计数，因此交换两个
加数不产生第二种表示。

### 下一项总是存在

考虑任意已有的有限严格递增正整数前缀。设最大项为 M，次大项为 S。
因为 0<S<M，整数 S+M 严格大于 M，且具有表示 S+M。

若某个表示 c+d=S+M 不含 M，那么 c≤S 且 d≤S，因此
c+d≤2S<S+M，矛盾。故表示必须含 M，另一项必为 S。由于 S<M，
这是由两个不同前项构成的唯一无序表示。

因此合法候选集合非空。自然数的良序性保证最小合法候选存在，且满足
M<a_next≤S+M<2M。对更新后的前缀重复同一构造即可无限进行。
每次新项严格增加，所以构造所得值的集合不可能包含于任何有限列表中。

### 定量计数下界

由 a₂=n 与每一步 a_next<2M，归纳得到

    a_(r+2) ≤ n·2^r，r≥0。

前 r+2 项互不相同，且全部不大于 a_(r+2)。若 A_n(X) 表示不大于 X 的
Ulam(1,n) 元素个数，则

    A_n(n·2^r) ≥ r+2。

Lean 文件将这一下界精确表示为从 Fin(r+2) 到相应 Ulam 值的单射，
并证明每个像都属于序列且不大于 n·2^r。因而这不是只证明一个有限前缀引理；
同一个完整递归序列同时满足最小选择规则、无穷性和计数估计。

上述计数下界是对数级估计。它不推出正自然密度，也不证明自然密度极限存在。

### 唯一性

若两个序列满足同一初值与最小选择规则，对项号作强归纳。前两项相同；若所有
前项已相同，则当前合法候选集合相同。两个下一项都是该集合的最小元，因而
相同。这证明所构造序列正是唯一的标准 Ulam(1,n) 序列。

## English proof

Fix n≥2. Start with a₁=1 and a₂=n. At every subsequent stage choose the least
integer larger than the previous term that has exactly one representation as
a sum of two distinct earlier values. Count an unordered pair once, by putting
the smaller summand first.

### Existence of every next term

For a finite strictly increasing positive prefix, let M be its largest value
and S its second-largest. Then S+M>M and S+M is a sum of two distinct earlier
values. If a representation c+d=S+M omitted M, both summands would be at most
S. This would give c+d≤2S<S+M, a contradiction. Thus every representation uses
M, and its other summand must be S. The representation is unique.

The set of eligible candidates is consequently nonempty. The well-ordering of
the natural numbers supplies its least member, and that member satisfies
M<a_next≤S+M<2M. Repeating the construction gives an actual sequence obeying
the least-choice rule at every stage. Its strict increase makes its range
infinite.

### Quantitative bound

Induction from a₂=n yields a_(r+2)≤n·2^r. The first r+2 terms are distinct and
all at most this bound. Hence, writing A_n(X) for the number of Ulam values at
most X, we obtain A_n(n·2^r)≥r+2.

The core Lean development expresses this count by an injection from
Fin(r+2) to values of the constructed sequence lying at or below n·2^r.
Its combined final theorem proves the rule, strict increase, infinitude,
growth bound, and counting statement for the same sequence.

Uniqueness follows by strong induction: matching earlier terms produce the
same eligible candidate set, whose least member is unique. The growth and
counting bounds do not claim positive natural density or a density limit.

## Attribution and exact scope

This is a formalization of an established elementary infinitude argument.
Daniel Ross's 2016 dissertation, *The Ulam Sequence and Related Phenomena*,
Chapter 1, printed pages 1–2 (PDF pages 10–11), describes the standard Ulam
rule and states the known infinitude fact. No novelty of that fact is claimed.

- Daniel Ross, University of Wisconsin–Madison, 2016:
  https://asset.library.wisc.edu/1711.dl/6DJJQWLMRTYIH8U/R/file-fb00e.pdf
- Competition conjecture 00000000205:
  https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/6ad05f1490626b518d19ad5c5603419f7a021d30/conjectures/00000000205.md

The repository adds the phrase “the infinitude is settled by density
estimates.” The formally verified quantitative content here is precisely the
logarithmic counting bound above. If its authors intend a stronger positive
density theorem, that stronger statement is not established by this package.

## 全局唯一表示 / Full-range uniqueness

对每一个非初始项 a_k（k≥3），若完整序列中的两个正数之和等于 a_k，
则它们都小于 a_k，故严格递增性保证它们都是较早项。因此在所有完整序列
元素中计算表示，与在此前缀中计算完全相同；恰有一个不同元素的无序对。
两个给定初始项不受这一表示条件约束。Lean 定理 sequence_global_uniqueSum
明确证明这一结论，无需增加假设。候选见证 S+M 不一定被选中，也不要求
它在后续步骤保持唯一表示。

For every non-seed term a_k (k≥3), any two full-range values summing to a_k
are positive and individually smaller than a_k. They therefore occur earlier.
The full-range and earlier-term representations of a selected term coincide.
The added Lean theorem sequence_global_uniqueSum proves this fact without new
hypotheses. The two seeds are prescribed exceptions. An unused witness S+M
need not retain uniqueness after further terms are added.

Clément and Steinerberger (2025), *Small gaps in the Ulam sequence*, §1.2,
p. 942 (PDF p. 3), explicitly confirm classical infinitude by the same
two-largest-terms argument. Thus infinitude itself is established; this does
not resolve stronger density questions.
https://comptes-rendus.academie-sciences.fr/mathematique/item/10.5802/crmath.746.pdf#page=3
