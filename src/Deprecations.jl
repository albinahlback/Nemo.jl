# Deprecated in 0.16.*

@deprecate ArbField(x::Int, y::Bool) ArbField(x, cached = y)

@deprecate AcbField(x::Int, y::Bool) AcbField(x, cached = y)

@deprecate prec(x::AcbMatSpace) precision(x)

@deprecate prec(x::ArbMatSpace) precision(x)

@deprecate prec(x::AcbPolyRing) precision(x)

@deprecate prec(x::ArbPolyRing) precision(x)

@deprecate prec(x::AcbField) precision(x)

@deprecate prec(x::ArbField) precision(x)

# Deprecated in 0.22.*

@deprecate binom(x::arb, n::UInt) binomial(x, n)

@deprecate binom(n::UInt, k::UInt, r::ArbField) binomial(n, k, r)

# Deprecated in 0.23.*

@deprecate modeta(x::acb) modular_eta(x)

@deprecate modweber_f(x::acb) modular_weber_f(x)

@deprecate modweber_f1(x::acb) modular_weber_f1(x)

@deprecate modweber_f2(x::acb) modular_weber_f2(x)

@deprecate modj(x::acb) modular_j(x)

@deprecate modlambda(x::acb) modular_lambda(x)

@deprecate moddelta(x::acb) modular_delta(x)

@deprecate ei(x::acb) exp_integral_ei(x)

@deprecate si(x::acb) sin_integral(x)

@deprecate ci(x::acb) cos_integral(x)

@deprecate shi(x::acb) sinh_integral(x)

@deprecate chi(x::acb) cosh_integral(x)

@deprecate li(x::acb) log_integral(x)

@deprecate expint(s::acb, x::acb) exp_integral_e(s, x)

@deprecate lioffset(x::acb) log_integral_offset(x)

@deprecate hyp1f1(a::acb, b::acb, x::acb) hypergeometric_1f1(a, b, x)

@deprecate hyp1f1r(a::acb, b::acb, x::acb) hypergeometric_1f1_regularized(a, b, x)

@deprecate hyperu(a::acb, b::acb, x::acb) hypergeometric_u(a, b, x)

@deprecate hyp2f1(a::acb, b::acb, c::acb, x::acb) hypergeometric_2f1(a, b, c, x)

@deprecate jtheta(z::acb, tau::acb) jacobi_theta(z, tau)

@deprecate ellipwp(z::acb, tau::acb) weierstrass_p(z, tau)

@deprecate ellipk(x::acb) elliptic_k(x)

@deprecate ellipe(x::acb) elliptic_e(x)

@deprecate barnesg(x::acb) barnes_g(x)
