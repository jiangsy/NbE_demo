-- the types
typ : Type
exp : Type

-- the constructors for typ
typ_bool : typ
typ_arr  : typ -> typ -> typ

-- the constructors for exp
exp_app   : exp -> exp -> exp
-- no type annotations for arguments
exp_abs   : (bind exp in exp) -> exp
exp_if    : typ -> exp -> exp -> exp -> exp
exp_true  : exp
exp_false : exp
