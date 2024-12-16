use anyhow::bail;

use crate::{
    expr::{self, mk_expr_app, mk_expr_assume, mk_expr_assump, mk_expr_take, Expr},
    kernel::{
        proof::{self, mk_type_prop},
        tt::{
            mk_app, mk_const, mk_local, mk_type_arrow, mk_type_const, mk_type_local, Def, Kind,
            LocalEnv, Name, Rec, Term, Type,
        },
    },
    parse::{FactInfo, Nasmespace, TokenTable},
    print::OpTable,
};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Fixity {
    Infix,
    Infixl,
    Infixr,
    Nofix,
    Prefix,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operator {
    pub symbol: String,
    pub fixity: Fixity,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Cmd {
    Infix(CmdInfix),
    Infixr(CmdInfixr),
    Infixl(CmdInfixl),
    Prefix(CmdPrefix),
    Nofix(CmdNofix),
    Def(CmdDef),
    Axiom(CmdAxiom),
    Lemma(CmdLemma),
    Const(CmdConst),
    TypeConst(CmdTypeConst),
    TypeVariable(CmdTypeVariable),
    Inductive(CmdInductive),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdInfix {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdInfixr {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdInfixl {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdPrefix {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdNofix {
    pub op: String,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdDef {
    pub name: Name,
    pub local_types: Option<Vec<Name>>,
    pub params: Vec<(Name, Type)>,
    pub ty: Type,
    pub target: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdAxiom {
    pub name: Name,
    pub local_types: Option<Vec<Name>>,
    pub params: Vec<(Name, Type)>,
    pub target: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdLemma {
    pub name: Name,
    pub local_types: Option<Vec<Name>>,
    pub params: Vec<(Name, Type)>,
    pub target: Term,
    pub holes: Vec<(Name, Type)>,
    pub expr: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdConst {
    pub name: Name,
    pub local_types: Option<Vec<Name>>,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdTypeConst {
    pub name: Name,
    pub kind: Kind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdTypeVariable {
    pub variables: Vec<Name>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdInductive {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub ctors: Vec<Constructor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constructor {
    pub name: Name,
    pub ty: Type,
}

#[derive(Debug, Clone, Default)]
pub struct Eval {
    pub proof_env: proof::Env,
    pub tt: TokenTable,
    pub ns: Nasmespace,
    pub pp: OpTable,
    pub tv: Vec<Name>,
}

impl Eval {
    pub fn run_cmd(&mut self, cmd: Cmd) -> anyhow::Result<()> {
        match cmd {
            Cmd::Infix(inner) => {
                let CmdInfix { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infix,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;
                Ok(())
            }
            Cmd::Infixr(inner) => {
                let CmdInfixr { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infixr,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;

                Ok(())
            }
            Cmd::Infixl(inner) => {
                let CmdInfixl { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infixl,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;

                Ok(())
            }
            Cmd::Prefix(inner) => {
                let CmdPrefix { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Prefix,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;
                Ok(())
            }
            Cmd::Nofix(inner) => {
                let CmdNofix { op, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Nofix,
                    prec: usize::MAX,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;
                Ok(())
            }
            Cmd::Def(inner) => {
                let CmdDef {
                    name,
                    local_types,
                    params,
                    mut ty,
                    mut target,
                } = inner;
                let need_shrink = local_types.is_none();
                if let Some(local_types) = &local_types {
                    for i in 0..local_types.len() {
                        for j in i + 1..local_types.len() {
                            if local_types[i] == local_types[j] {
                                bail!("duplicate type variables");
                            }
                        }
                    }
                }
                let mut local_env = LocalEnv {
                    local_types: local_types.unwrap_or_else(|| self.tv.clone()),
                    locals: vec![],
                    holes: vec![],
                };
                for (var, t) in params.iter().rev() {
                    target.abs(&[(*var, *var, t.clone())], true);
                    ty = mk_type_arrow(t.clone(), ty);
                }
                self.proof_env
                    .tt_env
                    .check_type(&mut local_env, &mut target, &mut ty)?;
                if need_shrink {
                    let mut shrinked_local_types = vec![];
                    for t in local_env.local_types {
                        if !ty.contains_local(&t) {
                            continue;
                        }
                        shrinked_local_types.push(t);
                    }
                    local_env.local_types = shrinked_local_types;
                }
                if self.proof_env.tt_env.consts.contains_key(&name) {
                    bail!("already defined");
                }
                self.ns.consts.insert(name, local_env.local_types.len());
                self.proof_env
                    .tt_env
                    .consts
                    .insert(name, (local_env.local_types.clone(), ty.clone()));
                self.proof_env.tt_env.defs.insert(
                    name,
                    Def {
                        local_types: local_env.local_types,
                        target,
                        hint: self.proof_env.tt_env.defs.len(),
                    },
                );
                Ok(())
            }
            Cmd::Axiom(inner) => {
                let CmdAxiom {
                    name,
                    local_types,
                    params,
                    mut target,
                } = inner;
                let need_shrink = local_types.is_none();
                if let Some(local_types) = &local_types {
                    for i in 0..local_types.len() {
                        for j in i + 1..local_types.len() {
                            if local_types[i] == local_types[j] {
                                bail!("duplicate type variables");
                            }
                        }
                    }
                }
                let mut local_env = LocalEnv {
                    local_types: local_types.unwrap_or_else(|| self.tv.clone()),
                    locals: vec![],
                    holes: vec![],
                };
                for (var, ty) in params.iter().rev() {
                    target.abs(&[(*var, *var, ty.clone())], true);
                    target = mk_app(
                        mk_const(Name::try_from("forall").unwrap(), vec![ty.clone()]),
                        target,
                    );
                }
                self.proof_env.tt_env.check_type(
                    &mut local_env,
                    &mut target,
                    &mut mk_type_prop(),
                )?;
                if need_shrink {
                    let mut shrinked_local_types = vec![];
                    for t in local_env.local_types {
                        if !target.contains_local_type(&t) {
                            continue;
                        }
                        shrinked_local_types.push(t);
                    }
                    local_env.local_types = shrinked_local_types;
                }
                if self.proof_env.facts.contains_key(&name) {
                    bail!("already defined");
                }
                self.ns.facts.insert(
                    name,
                    FactInfo {
                        type_arity: local_env.local_types.len(),
                        num_params: params.len(),
                    },
                );
                self.proof_env
                    .facts
                    .insert(name, (local_env.local_types, target));
                Ok(())
            }
            Cmd::Lemma(inner) => {
                let CmdLemma {
                    name,
                    local_types,
                    params,
                    mut target,
                    holes,
                    mut expr,
                } = inner;
                let need_shrink = local_types.is_none();
                if let Some(local_types) = &local_types {
                    for i in 0..local_types.len() {
                        for j in i + 1..local_types.len() {
                            if local_types[i] == local_types[j] {
                                bail!("duplicate type variables");
                            }
                        }
                    }
                }
                let mut local_env = LocalEnv {
                    local_types: local_types.unwrap_or_else(|| self.tv.clone()),
                    locals: vec![],
                    holes,
                };
                for (var, ty) in params.iter().rev() {
                    target.abs(&[(*var, *var, ty.clone())], true);
                    target = mk_app(
                        mk_const(Name::try_from("forall").unwrap(), vec![ty.clone()]),
                        target,
                    );
                    expr = mk_expr_take(*var, ty.clone(), expr);
                }
                self.proof_env.tt_env.check_type(
                    &mut local_env,
                    &mut target,
                    &mut mk_type_prop(),
                )?;
                if need_shrink {
                    let mut shrinked_local_types = vec![];
                    for t in local_env.local_types {
                        if !target.contains_local_type(&t) {
                            continue;
                        }
                        shrinked_local_types.push(t);
                    }
                    local_env.local_types = shrinked_local_types;
                }
                // auto insert 'change'
                let mut expr = mk_expr_app(
                    mk_expr_assume(target.clone(), mk_expr_assump(target.clone())),
                    expr,
                    target.clone(),
                );
                let mut h = expr::Env::new(
                    &self.proof_env.tt_env,
                    &mut local_env,
                    &self.proof_env.facts,
                )
                .elaborate(&mut expr)?;
                self.proof_env.check_prop(
                    &mut local_env,
                    &mut proof::Context::default(),
                    &mut h,
                    &target,
                )?;
                if self.proof_env.facts.contains_key(&name) {
                    bail!("already defined");
                }
                self.ns.facts.insert(
                    name,
                    FactInfo {
                        type_arity: local_env.local_types.len(),
                        num_params: params.len(),
                    },
                );
                self.proof_env
                    .facts
                    .insert(name, (local_env.local_types, target));
                Ok(())
            }
            Cmd::Const(inner) => {
                let CmdConst {
                    name,
                    local_types,
                    ty,
                } = inner;
                let need_shrink = local_types.is_none();
                if let Some(local_types) = &local_types {
                    for i in 0..local_types.len() {
                        for j in i + 1..local_types.len() {
                            if local_types[i] == local_types[j] {
                                bail!("duplicate type variables");
                            }
                        }
                    }
                }
                let mut local_env = LocalEnv {
                    local_types: local_types.unwrap_or_else(|| self.tv.clone()),
                    locals: vec![],
                    holes: vec![],
                };
                self.proof_env
                    .tt_env
                    .check_kind(&local_env, &ty, &Kind::base())?;
                if need_shrink {
                    let mut shrinked_local_types = vec![];
                    for t in local_env.local_types {
                        if !ty.contains_local(&t) {
                            continue;
                        }
                        shrinked_local_types.push(t);
                    }
                    local_env.local_types = shrinked_local_types;
                }
                if self.proof_env.tt_env.consts.contains_key(&name) {
                    bail!("already defined");
                }
                self.ns.consts.insert(name, local_env.local_types.len());
                self.proof_env
                    .tt_env
                    .consts
                    .insert(name, (local_env.local_types.clone(), ty.clone()));
                Ok(())
            }
            Cmd::TypeConst(inner) => {
                let CmdTypeConst { name, kind } = inner;
                if self.proof_env.tt_env.type_consts.contains_key(&name) {
                    bail!("already defined");
                }
                self.ns.type_consts.insert(name);
                self.proof_env.tt_env.type_consts.insert(name, kind);
                Ok(())
            }
            Cmd::TypeVariable(inner) => {
                let CmdTypeVariable { variables } = inner;
                for i in 0..variables.len() {
                    for j in i + 1..variables.len() {
                        if variables[i] == variables[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for v in &variables {
                    if self.tv.contains(v) {
                        bail!("type variable already defined");
                    }
                }
                self.tv.extend(variables);
                Ok(())
            }
            Cmd::Inductive(inner) => {
                let CmdInductive {
                    name,
                    local_types,
                    ctors,
                } = inner;
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                let mut local_env = LocalEnv {
                    local_types: local_types.clone(),
                    locals: vec![],
                    holes: vec![],
                };
                local_env.local_types.insert(0, name);
                for i in 0..ctors.len() {
                    for j in i + 1..ctors.len() {
                        if ctors[i].name == ctors[j].name {
                            bail!("duplicate constructors");
                        }
                    }
                }
                for ctor in &ctors {
                    self.proof_env
                        .tt_env
                        .check_kind(&local_env, &ctor.ty, &Kind::base())?;
                    let mut t = ctor.ty.clone();
                    let args = t.undischarge();
                    if t != mk_type_local(name) {
                        bail!("invalid constructor: {t}");
                    }
                    for mut a in args {
                        let xs = a.undischarge();
                        for x in &xs {
                            if x.contains_local(&name) {
                                bail!("constructor violates strict positivity");
                            }
                        }
                        if a != mk_type_local(name) && a.contains_local(&name) {
                            bail!("nested inductive type is unsupported");
                        }
                    }
                }
                if self.proof_env.tt_env.type_consts.contains_key(&name) {
                    bail!("already defined");
                }
                // Foo u v
                let target_ty = {
                    let mut c = mk_type_const(name);
                    c.apply(local_types.iter().map(|t| mk_type_local(*t)));
                    c
                };
                // Foo ↦ Foo u v
                let subst = [(name, &target_ty)];
                let mut cs = vec![];
                for ctor in &ctors {
                    let name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
                    if self.proof_env.tt_env.consts.contains_key(&name) {
                        bail!("already defined");
                    }
                    let mut ty = ctor.ty.clone();
                    ty.subst(&subst);
                    cs.push((name, ty));
                }
                self.ns.type_consts.insert(name);
                self.proof_env
                    .tt_env
                    .type_consts
                    .insert(name, Kind(local_types.len()));
                for (name, ty) in cs {
                    self.ns.consts.insert(name, local_types.len());
                    self.proof_env
                        .tt_env
                        .consts
                        .insert(name, (local_types.clone(), ty));
                }

                // generate the induction principle
                //
                // For the following definition of the type of ordinal numbers,
                //
                //   inductive ord : Type
                //   | limit : (ℕ → ord) → ord
                //   | succ : ord → ord
                //   | zero : ord
                //
                // the following induction principle is defined:
                //
                //   ind : ∀ α P,
                //           (∀ f, (∀ n, P (f n)) → P (limit f)) →
                //           (∀ α, P α → P (succ α)) →
                //           P zero →
                //           P α
                let pred = Name::fresh();
                let mut cases = vec![];
                for ctor in &ctors {
                    let mut args = vec![];
                    for arg in ctor.ty.clone().undischarge() {
                        args.push((Name::fresh(), arg));
                    }
                    // induction hypotheses
                    let mut ih_list = vec![];
                    for (arg_name, arg_ty) in &args {
                        let mut t = arg_ty.clone();
                        let mut xs = vec![];
                        for x in t.undischarge() {
                            xs.push((Name::fresh(), x));
                        }
                        if t != mk_type_local(name) {
                            continue;
                        }
                        // ∀ xs, P (a xs)
                        let mut a = mk_local(*arg_name);
                        a.apply(xs.iter().map(|(name, _)| mk_local(*name)));
                        let mut h = mk_local(pred);
                        h.apply([a]);
                        for (name, ty) in xs.into_iter().rev() {
                            h.abs(&[(name, name, ty.clone())], true);
                            let mut m = mk_const(Name::intern("forall").unwrap(), vec![ty]);
                            m.apply([h]);
                            h = m;
                        }
                        ih_list.push(h);
                    }
                    // ∀ args, {IH} → P (C args)
                    let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
                    let mut a = mk_const(
                        ctor_name,
                        local_types.iter().map(|t| mk_type_local(*t)).collect(),
                    );
                    a.apply(args.iter().map(|(name, _)| mk_local(*name)));
                    let mut target = mk_local(pred);
                    target.apply([a]);
                    for ih in ih_list.into_iter().rev() {
                        let mut m = mk_const(Name::intern("imp").unwrap(), vec![]);
                        m.apply([ih, target]);
                        target = m;
                    }
                    for (name, mut ty) in args.into_iter().rev() {
                        ty.subst(&subst);
                        target.abs(&[(name, name, ty.clone())], true);
                        let mut m = mk_const(Name::intern("forall").unwrap(), vec![ty]);
                        m.apply([target]);
                        target = m;
                    }
                    cases.push(target);
                }
                // ∀ x P, {cases} → P x
                let x = Name::fresh();
                let mut target = mk_local(pred);
                target.apply([mk_local(x)]);
                for case in cases.into_iter().rev() {
                    let mut m = mk_const(Name::intern("imp").unwrap(), vec![]);
                    m.apply([case, target]);
                    target = m;
                }
                for (name, nickname, ty) in [
                    (
                        pred,
                        Name::intern("P").unwrap(),
                        mk_type_arrow(target_ty.clone(), mk_type_prop()),
                    ),
                    (x, Name::intern("x").unwrap(), target_ty.clone()),
                ] {
                    target.abs(&[(name, nickname, ty.clone())], true);
                    let mut m = mk_const(Name::intern("forall").unwrap(), vec![ty]);
                    m.apply([target]);
                    target = m;
                }
                let ind_name = Name::intern(&format!("{}.ind", name)).unwrap();
                if self.proof_env.facts.contains_key(&ind_name) {
                    bail!("already defined");
                }
                self.ns.facts.insert(
                    ind_name,
                    FactInfo {
                        type_arity: local_types.len(),
                        num_params: 2,
                    },
                );
                self.proof_env
                    .facts
                    .insert(ind_name, (local_types.clone(), target));

                // generate the recursion principle
                //
                // For ord, the following recursor is defined:
                //
                //   rec.{u} : ord → ((ℕ → ord) → (ℕ → u) → u) → (ord → u → u) → u → u
                //
                // together with the following rules:
                //
                //   rec (limit f) ≡ λ k₁ k₂ k₃, k₁ f (λ x, rec (f x) k₁ k₂ k₃)
                //   rec (succ α) ≡ λ k₁ k₂ k₃, k₂ α (rec α k₁ k₂ k₃)
                //   rec zero ≡ λ k₁ k₂ k₃, k₃
                //
                let rec_ty_var = Name::fresh();
                let mut rec_local_types = local_types.clone();
                rec_local_types.push(rec_ty_var);
                let rec_name = Name::intern(&format!("{}.rec", name)).unwrap();
                let mut ctor_params_list = vec![];
                for ctor in &ctors {
                    let mut ctor_params = vec![];
                    let ctor_param_tys = ctor.ty.clone().undischarge();
                    for mut ctor_param_ty in ctor_param_tys {
                        ctor_param_ty.subst(&subst);
                        ctor_params.push((Name::fresh(), ctor_param_ty));
                    }
                    ctor_params_list.push(ctor_params);
                }
                let mut cont_params = vec![];
                for _ in &ctors {
                    cont_params.push(Name::fresh());
                }
                let mut cont_param_tys = vec![];
                let mut rhs_bodies = vec![];
                for ((ctor, cont), ctor_params) in ctors
                    .iter()
                    .zip(cont_params.iter())
                    .zip(ctor_params_list.iter())
                {
                    let mut cont_arg_tys = vec![];
                    let mut target = mk_local(*cont);

                    // pass the constructor arguments through
                    for (param, param_ty) in ctor_params {
                        cont_arg_tys.push(param_ty.clone());
                        target.apply([mk_local(*param)]);
                    }
                    // stepping
                    let ctor_arg_tys = ctor.ty.clone().undischarge();
                    for (ctor_arg, (param, _)) in ctor_arg_tys.into_iter().zip(ctor_params.iter()) {
                        let mut ctor_arg_target = ctor_arg.clone();
                        let arg_tys = ctor_arg_target.undischarge();
                        if ctor_arg_target != mk_type_local(name) {
                            continue;
                        }
                        let mut t = ctor_arg.clone();
                        t.subst(&[(name, &mk_type_local(rec_ty_var))]);
                        cont_arg_tys.push(t);

                        let binders: Vec<_> = arg_tys
                            .into_iter()
                            .map(|arg_ty| {
                                let name = Name::fresh();
                                (name, name, arg_ty)
                            })
                            .collect();
                        let mut m = mk_const(
                            rec_name,
                            rec_local_types.iter().map(|t| mk_type_local(*t)).collect(),
                        );
                        let mut a = mk_local(*param);
                        a.apply(binders.iter().map(|(x, _, _)| mk_local(*x)));
                        m.apply([a]);
                        m.apply(cont_params.iter().map(|k| mk_local(*k)));
                        m.abs(&binders, true);
                        target.apply([m]);
                    }

                    let mut cont_param_ty = mk_type_local(rec_ty_var);
                    cont_param_ty.discharge(cont_arg_tys);
                    cont_param_tys.push(cont_param_ty);

                    rhs_bodies.push(target);
                }
                let mut rec_ty = mk_type_local(rec_ty_var);
                rec_ty.discharge(cont_param_tys.clone());
                rec_ty.discharge([target_ty]);

                let rhs_binders = cont_params
                    .into_iter()
                    .zip(cont_param_tys)
                    .map(|(x, t)| (x, x, t))
                    .collect::<Vec<_>>();
                let mut recursors = vec![];
                let mut equations = vec![];
                for ((rhs_body, ctor_params), ctor) in rhs_bodies
                    .into_iter()
                    .zip(ctor_params_list.into_iter())
                    .zip(ctors.iter())
                {
                    let mut lhs = mk_const(
                        rec_name,
                        rec_local_types.iter().map(|t| mk_type_local(*t)).collect(),
                    );
                    let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
                    let mut lhs_arg = mk_const(
                        ctor_name,
                        local_types.iter().map(|t| mk_type_local(*t)).collect(),
                    );
                    lhs_arg.apply(ctor_params.iter().map(|(x, _)| mk_local(*x)));
                    lhs.apply([lhs_arg]);

                    let mut rhs = rhs_body;
                    rhs.abs(&rhs_binders, true);

                    recursors.push((
                        ctor_name,
                        Rec {
                            local_types: rec_local_types.clone(),
                            params: ctor_params.iter().map(|(x, _)| *x).collect(),
                            target: rhs.clone(),
                        },
                    ));

                    let mut eq =
                        mk_const(Name::intern("eq").unwrap(), vec![mk_type_local(rec_ty_var)]);
                    eq.apply([lhs, rhs]);

                    for (x, t) in ctor_params.into_iter().rev() {
                        eq.abs(&[(x, x, t.clone())], true);
                        let mut m = mk_const(Name::intern("forall").unwrap(), vec![t]);
                        m.apply([eq]);
                        eq = m;
                    }

                    equations.push(eq);
                }
                equations.reverse();
                let mut spec = equations.pop();
                for eq in equations.into_iter().rev() {
                    let mut conj = mk_const(Name::intern("and").unwrap(), vec![]);
                    conj.apply([spec.unwrap(), eq]);
                    spec = Some(conj);
                }

                if self.proof_env.tt_env.consts.contains_key(&rec_name) {
                    bail!("already defined");
                }
                self.ns.consts.insert(rec_name, rec_local_types.len());
                self.proof_env
                    .tt_env
                    .consts
                    .insert(rec_name, (rec_local_types.clone(), rec_ty));
                self.proof_env.tt_env.recursors.insert(rec_name, recursors);

                if let Some(spec) = spec {
                    let rec_spec_name = Name::intern(&format!("{}.rec.spec", name)).unwrap();
                    if self.proof_env.facts.contains_key(&rec_spec_name) {
                        bail!("already defined");
                    }
                    self.ns.facts.insert(
                        rec_spec_name,
                        FactInfo {
                            type_arity: rec_local_types.len(),
                            num_params: 0,
                        },
                    );
                    self.proof_env
                        .facts
                        .insert(rec_spec_name, (rec_local_types, spec));
                }
                Ok(())
            }
        }
    }
}
