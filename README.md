This is a Macaulay2 Package for handling representations of Young subgroups of the symmetric group, particularly in the multigraded setting.

A Young subgroup of the symmetric group $S_n$ is a product of smaller symmetric groups $S_{a_1} \times \dots \times S_{a_m} \leq S_n$. such that $\sum a_i = n$.
Representations, then, are induced from the smaller symmetric groups, the study of which is an application of Mackey theory.
This package particularly deals with the "multigraded" case, where each $S_\ell$ above is replaced with $G_\ell = S_\ell \ltimes (\mathbb{C}^*)^n$, where $C$ is the field of complex numbers.

Algorithms for tensor products, induction, and restriction are included, as well as computation of contingency tables. A more thorough description with examples can be found
as Appendix B of [my dissertation](https://curate.nd.edu/articles/dataset/Multigraded_and_Symmetric_Syzygies/28786148), included in this repository.
