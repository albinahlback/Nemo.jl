# Types of all Flint-backed matrices
const _FieldMatTypes = Union{QQMatrix, fpMatrix, FpMatrix, FqMatrix, fqPolyRepMatrix, FqPolyRepMatrix}
const _MatTypes = Union{_FieldMatTypes, ZZMatrix, zzModMatrix, ZZModMatrix}

################################################################################
#
#  Support for view(A, :, i) and view(A, i, :)
#
################################################################################

# MatrixView{MatrixType, ElemType}
struct MatrixView{S, T} <: AbstractVector{T}
  A::S
end

Base.length(V::MatrixView) = length(V.A)

Base.getindex(V::MatrixView, i::Int) = V.A[i]

Base.setindex!(V::MatrixView, z::ZZRingElem, i::Int) = (V.A[i] = z)

Base.setindex!(V::MatrixView, z, i::Int) = setindex!(V, ZZ(z), i)

Base.size(V::MatrixView) = (length(V.A), )

function Base.view(x::_MatTypes, r::Int, c::UnitRange{Int})
  A = view(x, r:r, c)
  return MatrixView{typeof(x), elem_type(base_ring(x))}(A)
end

function Base.view(x::_MatTypes, r::UnitRange{Int}, c::Int)
  A = view(x, r, c:c)
  return MatrixView{typeof(x), elem_type(base_ring(x))}(A)
end

################################################################################
#
#  Solve context functionality
#
################################################################################

# Make sure we don't use lazy_transpose for any flint backed type
function Solve.solve_context_type(NF::Solve.MatrixNormalFormTrait,
                                            ::Type{T}) where {T <: Union{
  ZZRingElem, QQFieldElem,
  fpFieldElem, FpFieldElem, FqFieldElem, fqPolyRepFieldElem, FqPolyRepFieldElem,
  zzModRingElem, ZZModRingElem,
  RealFieldElem, ArbFieldElem, ComplexFieldElem, AcbFieldElem}}
  MatType = dense_matrix_type(T)
  return Solve.SolveCtx{T, typeof(NF), MatType, MatType, MatType}
end

################################################################################
#
#  (No) lazy transpose
#
################################################################################

# Producing a LazyTransposedMatElem from a flint matrix should always be
# unintended because the resulting matrix will use generic code and not flint
Solve.lazy_transpose(A::_MatTypes) = transpose(A)

################################################################################
#
#  Solve context for matrices over finite fields
#
################################################################################

function Solve._can_solve_internal_no_check(::Solve.LUTrait, C::Solve.SolveCtx{T, Solve.LUTrait}, b::MatElem{T}, task::Symbol; side::Symbol = :left) where {T <: Union{fpFieldElem, FpFieldElem, FqFieldElem, fqPolyRepFieldElem, FqPolyRepFieldElem}}
  # Split up in separate functions to make the compiler happy
  if side === :right
    return Solve._can_solve_internal_no_check_right(Solve.LUTrait(), C, b, task)
  else
    return Solve._can_solve_internal_no_check_left(Solve.LUTrait(), C, b, task)
  end
end

function Solve._can_solve_internal_no_check_right(::Solve.LUTrait, C::Solve.SolveCtx{T, Solve.LUTrait}, b::MatElem{T}, task::Symbol) where {T <: Union{fpFieldElem, FpFieldElem, FqFieldElem, fqPolyRepFieldElem, FqPolyRepFieldElem}}
  LU = Solve.reduced_matrix(C)
  p = Solve.lu_permutation(C)
  pb = p*b
  r = rank(C)

  # Let A = matrix(C) be m x n of rank r. Then LU is build as follows (modulo
  # the permutation p).
  # For example, m = 5, n = 6, r = 3:
  #   (d b b b b b)
  #   (a d b b b b)
  #   (a a d b b b)
  #   (a a a 0 0 0)
  #   (a a a 0 0 0)
  #
  # L is the m x r matrix
  #   (1 0 0)
  #   (a 1 0)
  #   (a a 1)
  #   (a a a)
  #   (a a a)
  #
  # and U is the r x n matrix
  #   (d b b b b b)
  #   (0 d b b b b)
  #   (0 0 d b b b)
  # Notice that the diagonal entries d need not be non-zero!

  # Would be great if there were a `*_solve_lu_precomp` for the finite field
  # types in flint.

  x = similar(b, r, ncols(b))
  # Solve L x = b for the first r rows. We tell flint to pretend that there
  # are ones on the diagonal of LU (fourth argument)
  _solve_tril_right_flint!(x, view(LU, 1:r, 1:r), view(pb, 1:r, :), true)

  # Check whether x solves Lx = b also for the lower part of L
  if r < nrows(C) && view(LU, r + 1:nrows(LU), 1:r)*x != view(pb, r + 1:nrows(b), :)
    return false, zero(b, 0, 0), zero(b, 0, 0)
  end

  # Solve U y = x. We need to take extra care as U might have non-pivot columns.
  y = _solve_triu_right(view(LU, 1:r, :), x)

  fl = true
  if r < nrows(C)
    fl = Solve.permuted_matrix(C)*y == view(pb, r + 1:nrows(C), :)
  end

  if task !== :with_kernel
    return fl, y, zero(b, 0, 0)
  else
    return fl, y, kernel(C, side = :right)
  end
end

function Solve._can_solve_internal_no_check_left(::Solve.LUTrait, C::Solve.SolveCtx{T, Solve.LUTrait}, b::MatElem{T}, task::Symbol) where {T <: Union{fpFieldElem, FpFieldElem, FqFieldElem, fqPolyRepFieldElem, FqPolyRepFieldElem}}
  LU = Solve.reduced_matrix_of_transpose(C)
  p = Solve.lu_permutation_of_transpose(C)
  pbt = p*transpose(b)
  r = rank(C)

  x = similar(b, r, nrows(b))
  _solve_tril_right_flint!(x, view(LU, 1:r, 1:r), view(pbt, 1:r, :), true)

  # Check whether x solves Lx = b also for the lower part of L
  if r < ncols(C) && view(LU, r + 1:nrows(LU), 1:r)*x != view(pbt, r + 1:nrows(pbt), :)
    return false, zero(b, 0, 0), zero(b, 0, 0)
  end

  # Solve U y = x. We need to take extra care as U might have non-pivot columns.
  yy = _solve_triu_right(view(LU, 1:r, :), x)
  y = transpose(yy)

  fl = true
  if r < ncols(C)
    bp = b*p
    fl = y*Solve.permuted_matrix_of_transpose(C) == view(bp, :, r + 1:ncols(C))
  end

  if task !== :with_kernel
    return fl, y, zero(b, 0, 0)
  else
    return fl, y, kernel(C, side = :left)
  end
end

# Solves A x = B with A in upper triangular shape of full rank, so something
# like
#   ( + * * * * )
#   ( 0 0 + * * )
#   ( 0 0 0 + * )
# where + is non-zero and * is anything.
# This is a helper functions because flint can only do the case where the
# diagonal entries are non-zero.
function _solve_triu_right(A::MatT, B::MatT) where {MatT <: Union{fpMatrix, FpMatrix, FqMatrix, fqPolyRepMatrix, FqPolyRepMatrix}}
  @assert nrows(A) == nrows(B)
  pivot_cols = Int[]
  next_pivot_col = ncols(A) + 1
  @inbounds for r in nrows(A):-1:1
    for c in r:next_pivot_col - 1
      if !is_zero_entry(A, r, c)
        push!(pivot_cols, c)
        next_pivot_col = c
        break
      end
      if c == next_pivot_col - 1
        error("Matrix is not in upper triangular shape")
      end
    end
  end
  reverse!(pivot_cols)
  AA = reduce(hcat, view(A, 1:nrows(A), c:c) for c in pivot_cols; init = zero(A, nrows(A), 0))
  xx = similar(B, nrows(A), ncols(B))
  _solve_triu_right_flint!(xx, AA, B, false)
  x = zero(B, ncols(A), ncols(B))
  for i in 1:nrows(xx)
    view(x, pivot_cols[i]:pivot_cols[i], :) .= view(xx, i:i, :)
  end
  return x
end

################################################################################
#
#  Eigenvalues and eigenspaces
#
################################################################################

@doc raw"""
    eigenvalues(M::MatElem{T}) where T <: RingElem

Return the eigenvalues of `M` which lie in `base_ring(M)`.
"""
function eigenvalues(M::MatElem{T}) where T <: RingElem
  @assert is_square(M)
  K = base_ring(M)
  f = charpoly(M)
  return roots(f)
end

@doc raw"""
    eigenvalues_with_multiplicities(M::MatElem{T}) where T <: FieldElem

Return the eigenvalues of `M` (which lie in `base_ring(M)`) together with their
algebraic multiplicities as a vector of tuples of (root, multiplicity).
"""
function eigenvalues_with_multiplicities(M::MatElem{T}) where T <: RingElem
  @assert is_square(M)
  K = base_ring(M)
  Kx, x = polynomial_ring(K, "x", cached = false)
  f = charpoly(Kx, M)
  r = roots(f)
  return [ (a, valuation(f, x - a)) for a in r ]
end

@doc raw"""
    eigenvalues(L::Field, M::MatElem{T}) where T <: RingElem

Return the eigenvalues of `M` over the field `L`.
"""
function eigenvalues(L::Field, M::MatElem{T}) where T <: RingElem
  @assert is_square(M)
  M1 = change_base_ring(L, M)
  return eigenvalues(M1)
end

@doc raw"""
    eigenvalues_with_multiplicities(L::Field, M::MatElem{T}) where T <: RingElem

Return the eigenvalues of `M` over the field `L` together with their algebraic
multiplicities as a vector of tuples.
"""
function eigenvalues_with_multiplicities(L::Field, M::MatElem{T}) where T <: RingElem
  @assert is_square(M)
  M1 = change_base_ring(L, M)
  return eigenvalues_with_multiplicities(M1)
end

@doc raw"""
    eigenspace(M::MatElem{T}, lambda::T; side::Symbol = :left)
      where T <: FieldElem -> Vector{MatElem{T}}

Return a basis of the eigenspace of $M$ with respect to the eigenvalue $\lambda$.
If side is `:right`, the right eigenspace is computed, i.e. vectors $v$ such that
$Mv = \lambda v$. If side is `:left`, the left eigenspace is computed, i.e. vectors
$v$ such that $vM = \lambda v$.
"""
function eigenspace(M::MatElem{T}, lambda::T; side::Symbol = :left) where T <: FieldElem
  @assert is_square(M)
  N = deepcopy(M)
  for i = 1:ncols(N)
    N[i, i] -= lambda
  end
  return kernel(N, side = side)
end

@doc raw"""
    eigenspaces(M::MatElem{T}; side::Symbol = :left)
      where T <: FieldElem -> Dict{T, MatElem{T}}

Return a dictionary containing the eigenvalues of $M$ as keys and bases for the
corresponding eigenspaces as values.
If side is `:right`, the right eigenspaces are computed, if it is `:left` then the
left eigenspaces are computed.

See also `eigenspace`.
"""
function eigenspaces(M::MatElem{T}; side::Symbol = :left) where T<:FieldElem

  S = eigenvalues(M)
  L = Dict{elem_type(base_ring(M)), typeof(M)}()
  for k in S
    push!(L, k => vcat(eigenspace(M, k, side = side)))
  end
  return L
end

###############################################################################
#
#   Permutation
#
###############################################################################

# Unfortunately, there is no fmpq_mat_set_perm etc. in flint
function *(P::Perm, x::_FieldMatTypes)
  z = similar(x)
  t = base_ring(x)()
  @inbounds for i = 1:nrows(x)
    for j = 1:ncols(x)
      z[P[i], j] = getindex!(t, x, i, j)
    end
  end
  return z
end

function *(x::_FieldMatTypes, P::Perm)
  z = similar(x)
  t = base_ring(x)()
  @inbounds for i = 1:nrows(x)
    for j = 1:ncols(x)
      z[i, P[j]] = getindex!(t, x, i, j)
    end
  end
  return z
end

###############################################################################
#
#  Norm
#
###############################################################################

function norm(v::Union{AcbMatrix, ArbMatrix, ComplexMatrix, RealMatrix})
  return sqrt(sum(a^2 for a in v; init=zero(base_ring(v))))
end

################################################################################
#
#  Diagonal
#
################################################################################

@doc raw"""
    diagonal(A::MatrixElem{T}) -> Vector{T}

Return the diagonal of `A` as an array.
"""
diagonal(A::MatrixElem{T}) where {T} = T[A[i, i] for i in 1:min(nrows(A), ncols(A))]

function prod_diagonal(A::MatrixElem{T}) where {T}
  return prod(diagonal(A))
end

################################################################################
#
#  Reduce "modulo" RREF
#
################################################################################

@doc raw"""
    reduce_mod!(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem

For a reduced row echelon matrix $B$, reduce the rows of $A$ modulo $B$, i.e. all the pivot
columns will be zero afterwards.
"""
function reduce_mod!(A::MatElem{T}, B::MatElem{T}) where {T<:FieldElem}
  if is_rref(B)
    scale = false
  else
    scale = true
  end

  for h = 1:nrows(A)
    j = 1
    for i = 1:nrows(B)
      while iszero(B[i, j])
        j += 1
      end
      if scale
        A[h, :] -= A[h, j] * (inv(B[i, j]) * B[i, :])
      else
        A[h, :] -= A[h, j] * B[i, :]
      end
    end
  end
  return A
end

@doc raw"""
    reduce_mod(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem -> MatElem

For a reduced row echelon matrix $B$, reduce $A$ modulo $B$, i.e. all the pivot
columns will be zero afterwards.
"""
function reduce_mod(A::MatElem{T}, B::MatElem{T}) where {T<:FieldElem}
  C = deepcopy(A)
  reduce_mod!(C, B)
  return C
end


##################################################################
## Functions related to unimodularity verification
##################################################################

# ***SOURCE ALGORITHM***
# Refined implementation of method from
# Authors: C. Pauderis + A. Storjohann
# Title:   Detrministic Unimodularity Certification
# Where:   Proc ISSAC 2012, pp. 281--287
# See also: thesis of Colton Pauderis, 2013, Univ of Waterloo
#           Deterministic Unimodularity Certification and Applications for Integer Matrices


# add_verbosity_scope(:UnimodVerif) -- see func __init__ in src/Nemo.jl

#######################################################
# Low-level auxiliary functions -- should be elsewhere?
#######################################################

function _det(a::fpMatrix)
  a.r < 10 && return lift(det(a))
  #_det avoids a copy: det is computed destructively
  r = ccall((:_nmod_mat_det, Nemo.libflint), UInt, (Ref{fpMatrix}, ), a)
  return r
end

function map_entries!(a::fpMatrix, k::Nemo.fpField, A::ZZMatrix)
  ccall((:nmod_mat_set_mod, Nemo.libflint), Cvoid, (Ref{fpMatrix}, UInt), a, k.n)
  ccall((:fmpz_mat_get_nmod_mat, Nemo.libflint), Cvoid, (Ref{fpMatrix}, Ref{ZZMatrix}), a, A)
  a.base_ring = k  # exploiting that the internal repr is the indep of char
  return a
end

function Base.copy!(A::ZZMatrix, B::ZZMatrix)
  ccall((:fmpz_mat_set, Nemo.libflint), Cvoid, (Ref{ZZMatrix}, Ref{ZZMatrix}), A, B)
end

function Nemo.sub!(A::ZZMatrix, m::Int)
  for i=1:nrows(A)
    A_p = Nemo.mat_entry_ptr(A, i, i)
    sub!(A_p, A_p, m)
  end
  return A
end

# No allocations; also faster than *=
function Nemo.mul!(A::ZZMatrix, m::ZZRingElem)
  for i=1:nrows(A)
    A_p = Nemo.mat_entry_ptr(A, i, 1)
    for j=1:ncols(A)
      mul!(A_p, A_p, m)
      A_p += sizeof(Int)
    end
  end
  return A
end

@doc raw"""
    is_unimodular(A::ZZMatrix)
    is_unimodular(A::ZZMatrix; algorithm=:auto)

Determine whether `A` is unimodular, i.e. whether `abs(det(A)) == 1`.
The method used is either that of Pauderis--Storjohann or using CRT;
the choice is made based on cost estimates for the two approaches.

The kwarg `algorithm` may be specified to be `:CRT` or `:pauderis_storjohann`
to ensure that the corresponding underlying algorithm is used (after a quick
initial unimodularity check).  `:CRT` is better if the matrix is unimodular
and has an inverse containing large entries (or if it is not unimodular);
`:pauderis_storjohann` is asymptotically faster when the matrix is unimodular
and its inverse does not contain large entries, but it requires more space
for intermediate expressions.
"""
function is_unimodular(A::ZZMatrix; algorithm=:auto)
  # Call this function when no extra info about the matrix is available.
  # It does a preliminary check that det(A) is +/-1 modulo roughly 2^100.
  # If so, then delegate the complete check to is_unimodular_given_det_mod_m
  if !is_square(A)
    throw(ArgumentError("Matrix must be square"))
  end
  if !(algorithm in [:auto, :CRT, :pauderis_storjohann])
    throw(ArgumentError("algorithm must be one of [:CRT, :pauderis_storjohann, :auto]"))
  end
  # Deal with two trivial cases
  if nrows(A) == 0
    return true
  end
  if nrows(A) == 1
    return (abs(A[1,1]) == 1);
  end
  # Compute det mod M -- may later include some more primes
  target_bitsize_modulus = 100 # magic number -- should not be too small!
  @vprintln(:UnimodVerif,1,"Quick first check: compute det by crt up to modulus with about $(target_bitsize_modulus) bits")
  p::Int = 2^20 # start point of primes for initial CRT trial -- det with modulus >= 2^22 is much slower
  M = ZZ(1)
  det_mod_m = 0  # 0 means uninitialized, o/w value is 1 or -1
  A_mod_p = identity_matrix(Nemo.Native.GF(2), nrows(A))
  while nbits(M) <= target_bitsize_modulus
    @vprint(:UnimodVerif,2,".")
    p = next_prime(p + rand(1:2^10))  # increment by a random step to a prime
    ZZmodP = Nemo.Native.GF(p; cached = false, check = false)
    map_entries!(A_mod_p, ZZmodP, A)
    @vtime :UnimodVerif 2   det_mod_p = Int(_det(A_mod_p))
    if det_mod_p > p/2
      det_mod_p -= p
    end
    if abs(det_mod_p) != 1
      return false  # obviously not unimodular
    end
    if det_mod_m != 0 && det_mod_m != det_mod_p
      return false  # obviously not unimodular
    end
    det_mod_m = det_mod_p
    mul!(M, M, p)
  end
  return is_unimodular_given_det_mod_m(A, det_mod_m, M; algorithm=algorithm)
end #function


# THIS FUNCTION NOT OFFICIALLY DOCUMENTED -- not intended for public use.
function is_unimodular_given_det_mod_m(A::ZZMatrix, det_mod_m::Int, M::ZZRingElem; algorithm=:auto)
  # This UI is convenient for our sophisticated determinant algorithm.
  # We estimate cost of computing det by CRT and cost of doing Pauderis-Storjohann
  # unimodular verification then call whichever is likely to be faster
  # (but we avoid P-S if the space estimate is too large).
  # M is a modulus satisfying M > 2^30;
  # det_mod_m is det(A) mod M [!not checked!]: it is either +1 or -1.
  is_square(A) || throw(ArgumentError("Matrix must be square"))
  abs(det_mod_m) == 1 || throw(ArgumentError("det_mod_m must be +1 or -1"))
  M >  2^30 || throw(ArgumentError("modulus must be greater than 2^30"))
  (algorithm in [:auto, :CRT, :pauderis_storjohann]) || throw(ArgumentError("algorithm must be one of [:CRT, :pauderis_storjohann, :auto]"))
  # Deal with two trivial cases -- does this make sense here???
  nrows(A) == 0 && return true
  nrows(A) == 1 && return (abs(A[1,1]) == 1)
  @vprintln(:UnimodVerif,1,"is_unimodular_given_det_mod_m starting")
  if algorithm == :pauderis_storjohann
    @vprintln(:UnimodVerif,1,"User specified Pauderis_Storjohann --> delegating")
    return is_unimodular_Pauderis_Storjohann_Hensel(A)
  end
  n = ncols(A)
  Hrow = hadamard_bound2(A)
  Hcol = hadamard_bound2(transpose(A))
  DetBoundSq = min(Hrow, Hcol)
  Hbits = 1+div(nbits(DetBoundSq),2)
  @vprintln(:UnimodVerif,1,"Hadamard bound in bits $(Hbits)")
  if algorithm == :auto
    # Estimate whether better to "climb out" with CRT or use Pauderis-Storjohann
    CRT_speed_factor = 20.0  # scale factor is JUST A GUESS !!!  (how much faster CRT is compared to P-S)
    total_entry_size = sum(nbits,A)
    Estimate_CRT = ceil(((Hbits - nbits(M))*(2.5+total_entry_size/n^3))/CRT_speed_factor)  # total_entry_size/n is proportional to cost of reducing entries mod p
    EntrySize = maximum(abs, A)
    entry_size_bits = maximum(nbits, A)
    @vprintln(:UnimodVerif,1,"entry_size_bits = $(entry_size_bits)   log2(EntrySize) = $(ceil(log2(EntrySize)))")
    e = max(16, Int(2+ceil(2*log2(n)+log2(EntrySize))))  # see Condition in Fig 1, p.284 of Pauderis-Storjohann
    Estimate_PS = ceil(e*log(e)) # assumes soft-linear ZZ arith
    @vprintln(:UnimodVerif,1,"Est_CRT = $(Estimate_CRT)  and  Est_PS = $(Estimate_PS)")
    Space_estimate_PS = ZZ(n)^2 * e  # nbits of values, ignoring mem mgt overhead
    @vprintln(:UnimodVerif,1,"Space est PS: $(Space_estimate_PS)  [might be bytes]")
    if Estimate_PS < Estimate_CRT #=&& Space_estimate_PS < 2^32=#
      # Expected RAM requirement is not excessive, and
      # Pauderis-Storjohann is likely faster, so delegate to UniCertZ_hensel
      return is_unimodular_Pauderis_Storjohann_Hensel(A)
    end
  end
  if algorithm == :CRT
    @vprintln(:UnimodVerif,1,"User specified CRT --> delegating")
  end
  @vprintln(:UnimodVerif,1,"UnimodularVerification: CRT loop")
  # Climb out with CRT:
  # in CRT loop start with 22 bit primes; if we reach threshold (empirical), jump to much larger primes.
  p = 2^21; stride = 2^10; threshold = 5000000;
  A_mod_p = zero_matrix(Nemo.Native.GF(2), nrows(A), ncols(A))
  while nbits(M) < Hbits
    @vprint(:UnimodVerif,2,".")
    # Next lines increment p (by random step up to stride) to a prime not dividing M
    if p > threshold && p < threshold+stride
      @vprint(:UnimodVerif,2,"!!")
      p = 2^56; stride = 2^25;  # p = 2^56 is a good choice on my standard 64-bit machine
      continue
    end
    # advance to another prime which does not divide M:
    while true
      p = next_prime(p+rand(1:stride))
      if !is_divisible_by(M,p)
        break
      end
    end
    ZZmodP = Nemo.Native.GF(p; cached = false, check = false)
    map_entries!(A_mod_p, ZZmodP, A)
    det_mod_p = _det(A_mod_p)
    if det_mod_p > p/2
      det_mod_p -= p
    end
    if abs(det_mod_p) != 1 || det_mod_m != det_mod_p
      return false  # obviously not unimodular
    end
    M *= p
  end
  return true
end

# THIS FUNCTION NOT OFFICIALLY DOCUMENTED -- not intended for public use.
# Pauderis-Storjohann unimodular verification/certification.
# We use Hensel lifting to obtain the modular inverse B0
# Seems to be faster than the CRT prototype (not incl. here)
# VERBOSITY via :UnimodVerif
function is_unimodular_Pauderis_Storjohann_Hensel(A::ZZMatrix)
  n = nrows(A)
  # assume ncols == n
  EntrySize = maximum(abs, A)
  entry_size_bits = maximum(nbits, A)
  e = max(16, 2+ceil(Int, 2*log2(n)+entry_size_bits))
  ModulusLWB = ZZ(2)^e
  @vprintln(:UnimodVerif,1,"ModulusLWB is 2^$(e)")
  # Now look for prime: about 25 bits, and such that p^(2^sthg) is
  # just slightly bigger than ModulusLWB.  Bit-size of prime matters little.
  root_order = exp2(ceil(log2(e/25)))
  j = ceil(exp2(e/root_order))
  p = next_prime(Int(j))
  @vprintln(:UnimodVerif,1,"Hensel prime is p = $(p)")
  m = ZZ(p)
  ZZmodP = Nemo.Native.GF(p)
  MatModP = matrix_space(ZZmodP,n,n)
  B0 = lift(inv(MatModP(A)))
  mod_sym!(B0, m)
  delta = identity_matrix(base_ring(A), n)
  A_mod_m = identity_matrix(base_ring(A), n)
  @vprintln(:UnimodVerif,1,"Starting stage 1 lifting")
  while (m < ModulusLWB)
    @vprintln(:UnimodVerif,2,"Loop 1: nbits(m) = $(nbits(m))");
    copy!(A_mod_m, A)
    mm = m^2
    mod_sym!(A_mod_m,mm)
    @vtime :UnimodVerif 2  mul!(delta, A_mod_m, B0)
    sub!(delta, 1)
    divexact!(delta, m) # to make matrix product in line below cheaper
    @vtime :UnimodVerif 2 mul!(A_mod_m, B0, delta)
    mul!(A_mod_m, m)
    sub!(B0, B0, A_mod_m)
    m = mm
    mod_sym!(B0, m)
  end
  @vprintln(:UnimodVerif,1,"Got stage 1 modular inverse: modulus has $(nbits(m)) bits; value is $(p)^$(Int(round(log2(m)/log2(p))))")

  # Hadamard bound brings little benefit; anyway, almost never lift all the way
###  H = min(hadamard_bound2(A), hadamard_bound2(transpose(A)))
###  println("nbits(H) = $(nbits(H))");
  # Compute max num iters in k
  k = (n-1)*(entry_size_bits+log2(n)/2) - (2*log2(n) + entry_size_bits -1)
  k = 2+nbits(ceil(Int,k/log2(m)))
  @vprintln(:UnimodVerif,1,"Stage 2: max num iters is k=$(k)")

  ZZmodM,_ = residue_ring(ZZ,m; cached = false)  # m is probably NOT prime
  ##  @assert is_one(lift(MatModM(B0*A)))
  # Originally: R = (I-A*B0)/m
  R = A*B0
  sub!(R, 1) #this is -R, but is_zero test is the same, and the loop starts by squaring
  divexact!(R, m)
  if is_zero(R)
    return true
  end

  #ZZMatrix and ZZModMatrix are the same type. The modulus is
  #always passed in as an extra argument when needed...
  #mul! for ZZModMatrix is mul, followed by reduce.

  B0_modm = deepcopy(B0)
  mod_sym!(B0_modm, m)

  R_bar = zero_matrix(ZZ, n, n)
  M = zero_matrix(ZZ, n, n)

  @vprintln(:UnimodVerif,1,"Starting stage 2 lifting")
  for i in 0:k-1
    @vprintln(:UnimodVerif,1,"Stage 2 loop: i=$(i)")

    mul!(R_bar, R, R)
    #Next 3 lines do:  M = lift(B0_modm*MatModM(R_bar));
    mod_sym!(R_bar, m)
    mul!(M, B0_modm, R_bar)
    mod_sym!(M, m)
    # Next 3 lines do: R = (R_bar - A*M)/m; but with less memory allocation
    mul!(R, A, M)
    sub!(R, R_bar, R)
    divexact!(R, m)
    if is_zero(R)
      return true
    end
  end
  return false
end
