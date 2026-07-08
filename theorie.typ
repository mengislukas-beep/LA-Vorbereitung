#import "../../style.typ": *

#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#show: setup


#stdtitle(
  [Theorie],
  [das sollte man können],
  [Lukas Mengis],
)
#pagebreak()
= The rank theorem

Let
$
  T : V -> W 
$
be a linear map, where V is finite dim.
Then
$
  dim(ker(T)) + dim(im(T)) = dim(V)
$
Proof.

Write $n := dim(V)$.\
Let $u_1,dots, u_k$ be a basis for $ker(T)$
$
  span(u_1,dots,u_k) = ker(T) 
$
Extend the basis of $ker(T)$ to a basis for $V$
$
  span(u_1,dots, u_k, v_1,dots, v_(n-k))
$
We can write the image of $T$ as followed
$
  im(T) = span(T(u_1), dots ,T(u_k), T(v_1),dots,T(v_(n-k))) = span(T(v_1),dots,T(v_(n-k)))
$
We claim that $T v_1,dots, T v_(n-k) $ form a basis for $im(T)$. This proofs that $T  v_1,dots, T v_(n-k) $ spans $im(T)$, so it remains to show that those vectors are linear indep.\
Let $a_1, dots, a_(n-k) in K $, and assume $sum_(i=1)^(n-k)a_i T v_i = 0$.\
Since $T$ is linear
$
  T(sum_(i=1)^(n-k)a_i v_i) = sum_(i=1)^(n-k)a_i T v_i = 0\
  => sum_(i=1)^(n-k)a_i v_i in ker(T)
$
Note $u_1, dots, u_k$ is a basis for $ker(T)$
$
  =>ex b_1, dots ,b_k quad st a_1 v_1 + dots, a_(n-k) v_(n-k) = b_1 u_1 + dots + b_k u_k. \
  => a_1 v_1 + dots, a_(n-k) v_(n-k) - b_1 u_1 - dots - b_k u_k = 0
$
But $u_1, dots, u_k, v_1,dots,v_(n-k)$ are linear independent (they form a basis)
$
  => a_1=dots=a_(n-k) = b_1 = dots = b_k = 0 
$
This proves that 
$
  T v_1, dots , T v_(n-k)
$
form a basis for $im(T)$\
Conclusion 
$
  dim(T) = n-k = dim(V) - dim(ker(T))\
  dim(ker(T)) +dim(im(T)) = dim(V)
$
#align(right)[$square$]
#pagebreak()

= Dual Maps
== Lemma(18.a.7)

The elemnts 
$
  v_1^star, dots, v_n^star
$
form a basis for $V^star$\
We denote this basis by
$
  B^star = (v_1^star, dots, v_n^star)
$
Moreover 
$
  fa l in V^star, quad l = um l(v_i) v_i^star.
$
Proof.\
Let $l in V^star$. We claim that
$
  l &= um l(v_i) v_i^star \
  <=> l(v) &= um l(v_i) v_i^star (v)
$ 
Indeed, $l$ and its representative sum are linear maps $V->K$, so it's enough to check that in the second equation holds for $v=v_1, v=v_2,dots ,v=v_n$, bc $v_1,dots,v_n$ form a basis for $V$. \
Set $v=v_k$
$
  um l(v_i) v_i^star (v_k) = um l(v_i) delta_(i k) = l(v_k).
$ 
The cleaim just proven shows that $v_1^star, dots, v_n^star$ span $V^star$\
since 
$
  dim(V^star) = dim(V) = n,
$
it follows that $v_1^star,dots, v_n^star$ form a basis for $V^star$.
#proved
== Lemma & def. (18.a.9)

Let $V,W$ be vect. spaces oves $K$. Let
$
  T : V-> W
$
be a linear map. Define a new map 
$
  T^star : W^star -> V^star, quad T^star (l) := l compose T quad fa l in W^star \

  (l : W -> K)
$
Then $T^star$ is a linear map. It is called the dual map to T.\
Proof.\
Let $l in W^star$, i.e. $l : W -> K$ linear.\
Clearly $l compose T : V -> K$ is a linear map (b.c. both $T$ and $l$ are), so $T(l) := l compose T in V^star$. This shows  $T^star : W^star -> V^star$ has its target indeed $V^star$ as claimed.\ \
We'll show now that $T^star$ is a linear map.\
Let 
$
  l in W^star, quad alpha in K
$
We have that 
$ 
  T^star (alpha l) in V^star\
  => T^star (alpha l )(v) &= ((alpha l) compose T) (v)\
  &= (alpha l) (T v)\
  &= alpha l (T(v))\
  &= alpha(l compose T)(v)\
  &= alpha(T^star l)(v)
$
$
  => T^star (alpha l) = alpha T^star (l)
$
Similarly one shows
$
  T^star (l_1+l_2) (v) &= ((l_1+l_2) compose T) (v)\
  &=  (l_1 compose T + l_2 compose T) (v)\
  &= (l_1 compose T) (v) + (l_2 compose T) (v)\
  &= T^star(l_1) (v) + T^star (l_2) (v)
$
$
  => T^star (l_1+l_2) =  T^star (l_1) + T^star (l_2)
$
#proved
== Lemma (18.a.11)
Let 
$
  S : V-> W
$
be a linear map between two f.dim. Vect.spaces $V$ & $W$ over $K$. Let $Beta$ be a basis for $V$ and $Kappa$ a basis for $W$.\
Cosider
$
  S^star : W^star -> V^star
$
and the bases $Kappa^star, Beta^star$ for $W^star,V^star$, respectibely. \
Then
$
  [S^star]_(Beta^star)^(Kappa^star) = [S^Beta_Kappa]^T
$
Proof.\
Write
$
  Beta = (v_1,dots,v_n) , quad Kappa = (w_1dots, w_m)\
A :=[S]^Beta_Kappa,quad A = (a_(i j)). 
$
$A$ satisfies 
$
  S v_j = um a_(i j) w_i
$
Now for $w^star in Kappa^star$ we have
$
  S^star w_j^star &= w_j^star compose S\
  &= um (w_j^star compose S)(v_i) v_i^star\
  &=um w_j^star (S(v_i)) v_i ^star\
  &= um w_j^star (sum_(k=1)^n a_(k i) w_k) v_i^star = um a_(j i) v_i ^star 
$
$=>$ coordinates of $S^star w_j^star$ in the basis $Beta^star = (v_1^star,dots,v_n^star)$ are
$
  vec(a_(j 1), dots.v,a_(j n))
$ 
row j in $A$, represented as col in the matrix $A^T$

#proved 
#pagebreak()
= The isomorphism theorem (18.c.5)

Let $V,W$ be vect.sp.over $K$ and 
$
  T: v-> W
$
a linear map. Define a new map
$
  overline(T):  V slash_(ker(T)) -> im(T)
$
Let $x in V slash_(ker(T)) $. Choose a represantative $v in V$ for x.
$
  x = [v]
$
Define
$
  overline(T) (x) := T(v)
$
Then 
+ $overline(T)$ well defined , and is linear map.
+ $overline(T) : V slash_(ker(t)) -> im(T)$ is an isomorphism.
+ The following diagram cummutes

#align(center)[
  #diagram(cell-size: 15mm, 
  $
    V edge(T,->) edge("d", pi, ->) &W\
    V slash ker(T) edge(overline(T), ->) &im(T) edge("u",->, i)
  $)
]
Proof.  
== $overline(T)$ is well defined.\

Suppose $x = [v] = [v']$, we need to show that $T(v) = T(v')$.\
Indeed $[v] =[v']$ implies that 
$
  v-v' &in ker(T).\
  &=> T(v-v')=0\
  &=> T(v) = T(v')
$
== $overline(T)$ is linear

$
  overline(T) (alpha[v]) &= overline(T)([alpha v])\
  &= T(alpha v) \
  &= alpha T(v) = alpha overline(T) ([v])
$
$
  overline(T)([v_1]+ [v_2]) &= overline(T)([v_1+v_2])\
  &= T(v_1 +v_2)\
  &= T(v_1) + T(v_2) = T([v_1]) + T([v_2])
$
== $overline(T)$ is injective
Let $x in ker(overline(T))$. Write $x$ as $x = [v]$ for some $v in V$ 
.\
Then
$
  overline(T)(x) = T(v) => v in ker(T) => x = [v] = 0_(v slash_(ker(T)))
$


== $overline(T)$ is surjective

Let 
$
  w in im(T). quad => ex v in V st T(v) = w\
  => overline([v]) = T(v) = w
$
This shows that 
$
  im(T) subset.eq im(overline(T)).
$
But by the def. of $ overline(T)$ we also have $im(overline(T)) subset.eq im(T)$
$
  => im(overline(T)) = im(T).
$
== The commutativity of the diagram

This follows immediately from the definitions. 

#pagebreak()

= Determinant

== Definition of sgn of a permutation

Let 
$
  D : M_(n times n)(K) -> K
$
be an n-linear alternating function\
Denote
$
  I = ID = mat(bar.h epsilon_1 bar.h; dots.v;bar.h epsilon_n bar.h)
$
$B = (epsilon_1,dots, epsilon_n)$ is the standard basis of $K^n_("row")$
\
clearly

$
  alpha_i = um A (i,j) epsilon_j  quad fa 1<= i <= n 
$
$
  => D(A) &= D(alpha_1, dots, alpha_n) \
  &= D(sum_(j=1)^n A(1,j) epsilon_j , alpha_2, dots,alpha_n)\
  &= sum_(j=1)^n A (1,j) dot D(epsilon_j, alpha_2, dots, alpha_n)\
  &= sum_(j,k) A(1,j) dot A( 2,k) dot D(epsilon_j, epsilon_k, dots, alpha_n)\
  &= sum_(k_1,dots, k_n) (product_(j=1)^n A(j,k_j)) D(I)
$
Using the assumption that $D$ is alternating. $=>$ $D(epsilon_k_1,dots,epsilon_k_n)= n$ whenever two indices $k_1,dots,k_n$ are equal.\ 
So we are interested only in ordered sequence in which:
$
  fa  k_j != k_i quad fa i !=j
$
This is a permutation of degree n.\
We can think of it as a bijective function
$
  sigma : {1,dots, n} -> {1,dots, n}
$
then the sequence 
$
  (k_1, dots, k_n) = (sigma(1), dots, sigma(n))
$
is a permutaion as defined earlier.\
We can write 
$
  D(A) = sum_(sigma in S_n) A (1,sigma(1)) dot A(2,sigma(2))dot dots dot A(n,sigma(n)) D(epsilon_(sigma(1)), dots , epsilon_(sigma(n))) = sum_(sigma in S_n)  D(epsilon_(sigma(1)), dots , epsilon_(sigma(n))) product_(i =1)^n A(i,sigma(i))
 $
 \
 Let $sigma$ be a per utaion of degree n. Then on can pass from $(1, dots, n)$ to $(sigma(1), dots, sigma(n))$ by performing a finite sequence of interchanges of pairs (transposition).\
 More precisely, transposition is a permutation:
 $
   theta: {1,dots, n} -> {1,dots,n} quad 
 
 "for which" quad 
 
   ex i,j in {1,dots,n}, quad i != j\
   st  theta(i) = theta(j) "and" theta(k) = k quad fa k != i,j
 $
 Now, every permutation can be written as a composition of transpositions
 $
   sigma = theta_1 compose dots compose theta_m
 $
 The transposition are not unique. There are many different way
 $
   sigma = theta_1 compose dots compose theta_m = theta'_1 compose dots compose theta'_m'
 $
 To show there are many different ways we can look at examples
 $
   sigma := (1,2,3) -> (3,2,1) 
 $
 $
   sigma = t_(0,1) compose t_(1,2) compose t_(0,1) = t_(0,2)
 $
 == Lemma (20.b.1)
 If a permutation is obtained from two different ways, one time by a sequence of $m$ permutations, and another time by a sequnce of $m'$ transposition, the $m$ and $m'$ have the same parity
 $
   (-1)^m = (-1)^m'
 $
 The parity only depends on $sigma$ and not on the a particular way we performed a seq. of transpositions.
 Note 
 $
   sgn(sigma) := (-1)^m  quad fa m   
 $\
 Proof\
 Fix a determinant funct. 
 $
   E: M_(n times n) (K) -> K
 $
 consider 
 $
   E(e_(sigma(1)), dots, e_(sigma(n)))
 $
 If $(sigma(1), dots, sigma(n))$ can be obtained from $(1,dots, n)$ by a sequence of $m$ transposition then the matrix 
  $
    mat(bar.h, e_(sigma(1)), bar.h;,dots.v,;bar.h,e_sigma(n),bar.h)
  $
  can be obtained from I = $mat(bar.h,e_1,bar.h;,dots.v,;bar.h,e_n,bar.h)$ by a seuqnce of interchanges of m pairs of rows.
  $
    =>E(e_(sigma(1)), dots, e_(sigma(n))) &= (-1)^m E(e_1,dots,e_n) = (-1)^m E(I) = (-1)^m quad fa m
  $
  $
    => m = m'
  $
  $
    => D(A) = sum_(sigma in S_n) sgn(sigma) product_(i=1)^n A(i,sigma(1))
  $

== 20.b.5
$
  fa A,B in M_(n times n) (K) "we have" quad det(A dot B) = det(A) dot det(B)
$
Proof\
Fix a mat $B in M_(n times n) (K)$, and consider a funct.
$
  D: M_(n times n) (K) -> K\
  D(A) := det(A dot B)
$
Claim D is n-linear and alternating.\
Proof of claim\
Write
$
  A = mat(bar.h, alpha_1, bar.h;,dots.v,;bar.h,alpha_n,bar.h)
$
If we vies $alpha_i$ as an $1 times n$ matrix then $alpha_1 dots B$ is also $1 times n$, and in fact 
$
  A dot B = mat(bar.h, alpha_1 dot B, bar.h;,dots.v,;bar.h,alpha_n dot B, bar.h)
$
So 
$
  D(A) = det ( alpha_1, dot B, dots, alpha_n dot B)
$
Clearly $fa$ two row vector
\
gefällt mir nicht mache einen anderen Beweis\ \
Proof\
Let $A,B,C in M_(n times n) (K)$, define
$
  C = A B
$ 
using matrix multiplication
$
  c_(i,j) =  sum_(K=1)^n a_(i,k) b_(k,j)
$
Therefore
$
  det(C) &= det(A B)\
  &= sum_(sigma in S_n) sgn(sigma) product^n_(i=1) c_(i,sigma(i))\
  &= sum_(sigma in S_n) sgn(sigma) product^n_(i=1) (sum_(k_i)^n a_(i,k_i)b_(k_i, sigma(i)))\
  &=sum^n_(k_1,dots,k_n)  product_(i=1)^n a_(i,k_i) underbrace(sum_(sigma in S_n) sgn(sigma)product_(i=1)^n b_(k_i,sigma(i)), k_i = k_j =>quad  =0 )
$
If $k_i = k_j$ then the right site is $=0$, therefore we can change to assuming permutation
$
  =>   dots =(sum_(pi in S_n) product^n_(i=1) a_(i,pi(i))) (sum_(sigma in S_n) sgn(sigma) product_(i=1)^n b_(pi(i), sigma(i)))\
$
Let $sigma = tau compose pi in S_n$, with $tau in S_n$
$
  => dots &=(sum_(pi in S_n) product^n_(i=1) a_(i,pi(i))) (sum_(tau compose pi in S_n) sgn(tau compose pi) product_(i=1)^n b_(pi(i), (tau compose  pi) (i)))\
$

Since $pi$ is a permutation, we may reindex the product, and since multiplication in K is commutative, the order of the factors does not matter. Note that  $sgn(pi compose tau) = sgn(pi) sgn(tau)$.  
$
  =>dots &=(sum_(pi in S_n) sgn(pi) product^n_(i=1) a_(i,pi(i))) (sum_(tau  in S_n) sgn(tau) product_(j=1)^n b_(j, tau  (j))) = det(A) det(B)
$
(Since $sgn(pi)$ is independent of $tau$, it can be factored out of the inner sum and absorbed into the outer sum over $pi$.)

== 20.b.3
$fa$ n-linear. alternating function 
$
  D: M_(n times n) (K) -> K
$
Let $A in M_(n times n) (K)$
$
  => alpha_i = um A(i,j) e_j quad fa 1<=i <=n 
$
we have 
$
  D(A) &= D(alpha_1, dots, alpha_n)\
  &= sum_(i_1,dots,i_n) product_(k=1)^n a(i_k,k) D(e_i_1, dots, e_i_n)
$

Since $D$ is alternating every therm with equal indices vanishes. We can witch to permutation.
$
  => D(A) = sum_(sigma in S_n) product_(k=1)^n a(sigma(k),k) D(e_sigma(1), dots, e_sigma(n))
$
Since D is alternating
$
   D(e_sigma(1), dots, e_sigma(n)) = sgn(sigma) D(I)
$
therefore
$
  D(A) &= (sum_(sigma in S_n) sgn(sigma) product_(i=1)^n a(sigma(i),i)) D(I)\ 
  &= det(A) D(I)
$

== Determinants of endomorphisms

Let 
$
  A in M_(n times n) (K) quad "and" quad P in G L (n,K) 
$
Then
$
  det(P^(-1) A P) &= det(P^(-1)) det(A) det (P)\
  &= 1/(det(P)) det(A) det(P) = det(A)
$
$=>$ similar matrices have the same determinant.

\
\
Let $V$ be a finit dim. vect space over $K$. Put $n:=dim(V)$.
Let 
$
  T: V-> V quad "a linear map"
$
Pick a basis $B$ for $V$. This gets us a matrix $[T]_B^B in M_(n times n) (K)$.\ 
Consider $det([T]_B^B)$.\
 Does $det([T]_B^B)$ depend on $B$?\
 Let $B'$ another basis for $V$. Denote by
 $
   P := [idv]_B^B'
 $
 the transition mat. between the basis $B'$ and $B$.\
 Recall that
 $
   [T]_B'^B' = [idv]_B'^B dot[T]_B^B dot [idv]_B^B'
 $ 
 and also we have
 $
   [idv]_B'^B = ([idv]_B^B')^(-1)
 $
 So
 $
   [T]_B'^B' = P^(-1) [T]_B^B P => det([T]_B^B) = det([T]_B'^B')
 $
 == Recall

For linear maps $S,T:V -> V$ and a basis $B$:

$
[S compose T]^B_B = [S]^B_B [T]^B_B
$

If $T$ is an isomorphism,

$
[T^(-1)]^B_B = ([T]^B_B)^(-1).
$

The identity map is represented by the identity matrix:

$
[id_V]^B_B = I.
$
= Eigenvalues and Eigenvectors

== 20.a.4

Let $lambda_1, dots, lambda_n$ be pairwise distinct eigenvalues of $T$ with eigenvectors $v_1, dots, v_n$.

We prove by induction on $n$.

Base case $n=1$: since $v_1 != 0$, the set ${v_1}$ is linearly independent.

Induction step: Assume $v_1, dots, v_n$ are linearly independent.  
Let

$
a_1 v_1 + dots + a_n v_n + a_(n+1) v_(n+1) = 0. quad (star)
$

Apply $T$:

$
a_1 lambda_1 v_1 + dots + a_n lambda_n v_n
+ a_(n+1) lambda_(n+1) v_(n+1) = 0. quad (**)
$

Now compute $(**) - lambda_(n+1) (*)$:

$
a_1 (lambda_1 - lambda_(n+1)) v_1
+ dots +
a_n (lambda_n - lambda_(n+1)) v_n
= 0.
$

By the induction hypothesis,

$
a_i (lambda_i - lambda_(n+1)) = 0
quad forall i = 1, dots, n.
$

Since $lambda_i != lambda_(n+1)$,

$
a_1 = dots = a_n = 0.
$

Substitute into $(*)$:

$
a_(n+1) v_(n+1) = 0.
$

Since $v_(n+1) != 0$,

$
a_(n+1)=0.
$

Thus

$
a_1 = dots = a_n = a_(n+1)=0,
$

so $v_1, dots, v_n, v_(n+1)$ are linearly independent.

= Trace
== Lemma 21.a.10

$
  fa A,B in M_(n times n) (K) \
  Tr(A dot B) = Tr(B dot A)
$
If $A$ and $B$ are similar matrices then 
$
  Tr(A) = Tr(B)
$
In particular, if $B$ ab $B'$ are two bases for $V$ then 
$
  Tr([T]_B^B) = Tr([T]_B'^B')
$ 
Thus, $Tr(T)$ is well-defined.\
Proof
\
1)
$
  Tr(A dot B) &= um (A dot B)_(i,i)\
  &= um sum_(j=1)^n A_(i j)B_(j i)\
  &= sum_(i,j) A_(i j) B_(j i)\
  &=sum_(i,j) A_(j i) B_(i j)\
  &= um sum_(j=1)^n A_(j i)B_(i j)\
  &= um (B dot A)_(i i) = Tr(B dot A)
$
2)
If $B = P^(-1) A P$ then
$
  Tr(B) &= Tr(P^-1 A P)\
  &= Tr(P^-1 dot ( A P))\
  &underbrace(=, "by "1) Tr(A P P^(-1)) = Tr(A)
$
3)
$
  Tr([T]_B'^B') &= Tr([idv]_B'^B dot  [T]_B^B dot [idv]_B'^B)\
  & underbrace(=, "by "1) Tr([T]_B^B)
$

== Geometric and algebraic multiplicities of eigenvalues (21.b3/22.b4)


Let $lambda$ be an eigenvalue of $T in End(V)$.

$
m_g (T;lambda)
=
dim(E_T (lambda)).
$

If $V$ is finite-dimensional,

$
m_a (T;lambda)
=
"multiplicity of " lambda " in " P_T (x).
$
Prob (21.b.4)
$
  m_g (T; lambda) <= m_a (T; lambda)
$
Proof\

Let

$
k = m_g(T;lambda)=dim(E_T(lambda)).
$

Choose a basis

$
(v_1,dots,v_k)
$

of $E_T(lambda)$ and extend it to a basis

$
B=(v_1,dots,v_k,w_(k+1),dots,w_n)
$

of $V$.

Then

$
[T]^B_B= mat(bar, , bar; [T v_1]_B,dots,[T v_n]_B;bar,,bar) =

mat(lambda I_k, star;0,C)

$
where $C in M_((n-k) times (n-k)) (K)$

Hence

$
P_T(x)
=
det([T]^B_B-x I_n)
=(lambda-x)^k det(C-x I_(n-k)).
$

Therefore,

$
(lambda-x)^k bar P_T (x),
$

so $lambda$ is a root of $P_T (x)$ of multiplicity at least $k$:

$
m_a (T;lambda) >= k.
$

Since

$
k=m_g (T;lambda),
$

we conclude

$
m_g (T;lambda) =k <= m_a (T;lambda).
$

#align(right)[$square$] 

= The orthogonal Complement

Let $(V, ip(.,.))$ be an inner product space over $(#R "or" #C)$

== def 22.b.1
Let $nothing != S subset.eq V$ be a subset. The orthogonal complement os $S$ is defined as followed.
$
  S^perp := {v in V bar v perp s quad fa s in S} = {v in V bar ip(v,s)=0}
$
When 
$
  S ={v} quad " we write" v^perp := {v}^perp
$

proof\
1) $S^perp subset.eq V$ is a linear subspace

$
  0 in S^perp "b.c." ip(0,s) =0 quad fa s in S\

$
If $alpha,beta in K, v,w in S^perp$ then $fa s in S$ we have 
$
  ip(alpha v + beta w,s) = alpha ip(v,s) 1 beta ip(w,s) = 0 => alpha v + beta w in S^perp
$
2) $0^perp = V, V^perp ={0}$\
$0^perp = V$ 
$
  0^perp = {v in V bar ip(0,v) = 0} = V
$
Let $v in V^perp. => ip(v,w) = 0 quad w in V$. In particular 
$
  ip(v,v) = 0 => v = 0
$ 
This shows $V^perp subset.eq {0}$. But clearly ${0} in V^perp$. So $V^perp = {0}$.\
3) $S inter S^perp$ is either $nothing$ or equal to ${0}$\
If $S inter S^perp- = nothing$ we are done. otherwise, assume that $s in S inter S^perp => ip(s,s)= 0 => s =0$\
4) If $S subset.eq T$ then $S^perp supset.eq T^perp$\
Let $s in T^perp$
$
  ip(s,t) = 0 quad fa t in T
$
Since 
$
  S subset.eq T
$
this holds $fa s in S$.\


so
$
  T^perp subset.eq S^perp
$
5) $("Sp"(S))^perp = S^perp$\
We have $S subset.eq span(S)$.\
By 4),
$
(span(S))^perp subset.eq S^perp.
$

We'll show that
$
S^perp subset.eq (span(S))^perp.
$

Indeed, let $v in S^perp$.

Let $u in span(S)$. Write
$
u = sum_(i=1)^k alpha_i u_i
$
with $alpha_i in K$ and $u_i in S$.

Then
$
ip(v, u)
= sum_(i=1)^k alpha_i ip(v, u_i)
= 0.
$

Hence
$
v in (span(S))^perp.
$

Therefore
$
(span(S))^perp = S^perp.
$


6) Let $s in S$.

Then for all $v in S^perp$ we have
$
ip(v, s) = 0.
$

Hence
$
ip(s, v) = 0.
$

So
$
s in (S^perp)^perp.
$

Thus
$
S subset.eq (S^perp)^perp.
$