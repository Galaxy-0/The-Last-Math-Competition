# 00000000425

**English.** Definition: The generating function of boxed plane partitions is MacMahon's three-parameter product. Conjecture: The coefficient sequence of the diagonal specialization always satisfies coefficientwise log-concavity; and equality in the concavity holds only at the diagonal single cell. (diagonal coefficient log-concavity)

**中文。** 定义：盒装平面分拆的母函数为 MacMahon 三参数乘积。猜想：对角特殊化的系数序列恒满足逐系数对数凹不等式；且凹性的等号仅在对角单格。（对角系数对数凹）

## Provenance

Original bilingual statement at commit `f180f64ae3fca8e87d70c61ed7fd674775f050ca`.

https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/f180f64ae3fca8e87d70c61ed7fd674775f050ca/conjectures/00000000425.md

## Interpretation and scope

Diagonal specialization means equal box side lengths. The proof covers both numerical coefficient log-concavity for a fixed cubic box and coefficientwise log-concavity across successive cubic box sizes. Lean constructs the actual infinite quotients, proves their full numerator/denominator equations, and proves the finite-prefix correspondence needed for the negative coefficient.
