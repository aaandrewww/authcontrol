# authcontrol
Class project using an authorization logic in the kernel as an access control mechanism.

Access control in JOS is overly restrictive and mandatory. System calls that modify an environment may only be invoked by the the environment itself or its immediate ancestor. As a result, applications that do not have a clear hierarchical structure must use IPC for all inter-process communication. In particular, sharing memory requires per-page synchronization through IPC calls.

Authorization logics are a principled technique for implementing rule-based access control mecha- nisms. They have several advantages over traditional OS access control mechanisms such as access control lists. In particular, they allow principals to express access control decisions for which they do not have complete information. Authorization logics also provide proof-carrying authorization. That is, the capability to access a resource carries with it the set of authorization decisions that granted it.

To help ensure the correctness of our proof checker, we first implemented it in the Coq Proof Assistant. This enabled us to prove that our proof checker was correct, as well as work out some of the implementation details in a strongly typed language.

We showed the feasibility of using authorization logic as an OS-level access control mechanism by implementing it in JOS. We found that its performance was comparable to existing mechanisms in JOS, particularly if the results of proof-checking are cached by the kernel.
