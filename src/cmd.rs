use std::iter::zip;

use anyhow::bail;

use crate::{
    expr::{self, mk_expr_app, mk_expr_assume, mk_expr_assump, mk_expr_take, Expr},
    kernel::{
        proof::{self, mk_type_prop, Forall, Imp},
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
    TypeInductive(CmdTypeInductive),
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
pub struct CmdTypeInductive {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub ctors: Vec<DataConstructor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DataConstructor {
    pub name: Name,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdInductive {
    pub name: Name,
    pub local_types: Option<Vec<Name>>,
    pub params: Vec<(Name, Type)>,
    pub target_ty: Type,
    pub ctors: Vec<Constructor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constructor {
    pub name: Name,
    pub params: Vec<(Name, Type)>,
    pub target: Term,
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
    fn add_const(&mut self, name: Name, local_types: Vec<Name>, ty: Type) {
        self.ns.consts.insert(name, local_types.len());
        self.proof_env.tt_env.consts.insert(name, (local_types, ty));
    }

    fn add_axiom(&mut self, name: Name, local_types: Vec<Name>, num_params: usize, target: Term) {
        self.ns.facts.insert(
            name,
            FactInfo {
                type_arity: local_types.len(),
                num_params,
            },
        );
        self.proof_env.facts.insert(name, (local_types, target));
    }

    fn add_type_const(&mut self, name: Name, kind: Kind) {
        self.ns.type_consts.insert(name);
        self.proof_env.tt_env.type_consts.insert(name, kind);
    }

    fn has_const(&self, name: Name) -> bool {
        self.proof_env.tt_env.consts.contains_key(&name)
    }

    fn has_axiom(&self, name: Name) -> bool {
        self.proof_env.facts.contains_key(&name)
    }

    fn has_type_const(&self, name: Name) -> bool {
        self.proof_env.tt_env.type_consts.contains_key(&name)
    }

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
                if self.has_const(name) {
                    bail!("already defined");
                }
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
                self.add_const(name, local_env.local_types.clone(), ty.clone());
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
                if self.has_axiom(name) {
                    bail!("already defined");
                }
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
                self.add_axiom(name, local_env.local_types, params.len(), target);
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
                if self.has_axiom(name) {
                    bail!("already defined");
                }
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
                self.add_axiom(name, local_env.local_types, params.len(), target);
                Ok(())
            }
            Cmd::Const(inner) => {
                let CmdConst {
                    name,
                    local_types,
                    ty,
                } = inner;
                if self.has_const(name) {
                    bail!("already defined");
                }
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
                self.add_const(name, local_env.local_types, ty);
                Ok(())
            }
            Cmd::TypeConst(inner) => {
                let CmdTypeConst { name, kind } = inner;
                if self.has_type_const(name) {
                    bail!("already defined");
                }
                self.add_type_const(name, kind);
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
            Cmd::TypeInductive(cmd) => self.run_type_inductive_cmd(cmd),
            Cmd::Inductive(cmd) => self.run_inductive_cmd(cmd),
        }
    }

    fn run_type_inductive_cmd(&mut self, cmd: CmdTypeInductive) -> anyhow::Result<()> {
        let CmdTypeInductive {
            name,
            local_types,
            ctors,
        } = cmd;
        if self.has_type_const(name) {
            bail!("already defined");
        }
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
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            if self.has_const(ctor_name) {
                bail!("already defined");
            }
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
        let ind_name = Name::intern(&format!("{}.ind", name)).unwrap();
        if self.has_axiom(ind_name) {
            bail!("already defined");
        }
        let rec_name = Name::intern(&format!("{}.rec", name)).unwrap();
        if self.has_const(rec_name) {
            bail!("already defined");
        }
        let rec_spec_name = Name::intern(&format!("{}.rec.spec", name)).unwrap();
        if !ctors.is_empty() && self.has_axiom(rec_spec_name) {
            bail!("already defined");
        }
        // well-formedness check is completed.

        // generate type constructor
        self.add_type_const(name, Kind(local_types.len()));

        // generate data constructors
        let target_ty = {
            // Foo u v
            let mut c = mk_type_const(name);
            c.apply(local_types.iter().map(|t| mk_type_local(*t)));
            c
        };
        // Foo ↦ Foo u v
        let subst = [(name, &target_ty)];
        let mut cs = vec![];
        for ctor in &ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            let mut ty = ctor.ty.clone();
            ty.subst(&subst);
            cs.push((ctor_name, ty));
        }
        for (name, ty) in cs {
            self.add_const(name, local_types.clone(), ty);
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
        let motive = Name::fresh();
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
                let mut h = mk_local(motive);
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
            let mut target = mk_local(motive);
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
        let mut target = mk_local(motive);
        target.apply([mk_local(x)]);
        for case in cases.into_iter().rev() {
            let mut m = mk_const(Name::intern("imp").unwrap(), vec![]);
            m.apply([case, target]);
            target = m;
        }
        for (name, nickname, ty) in [
            (
                motive,
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
        self.add_axiom(ind_name, local_types.clone(), 2, target);

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

            let mut eq = mk_const(Name::intern("eq").unwrap(), vec![mk_type_local(rec_ty_var)]);
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

        self.add_const(rec_name, rec_local_types.clone(), rec_ty);
        self.proof_env.tt_env.recursors.insert(rec_name, recursors);

        if let Some(spec) = spec {
            self.add_axiom(rec_spec_name, rec_local_types, 0, spec);
        }
        Ok(())
    }

    fn run_inductive_cmd(&mut self, cmd: CmdInductive) -> anyhow::Result<()> {
        // Given the following inductive predicate:
        //
        //   inductive P.{u} (x : τ) : σ → Prop
        //   | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        //
        // the following set of delcarations is generated:
        //
        //  const P.{u} : τ → σ → Prop
        //  axiom P.intro.{u} (x : τ) : ∀ y, φ → (∀ z, ψ → P.{u} x M) → P.{u} x N
        //  axiom P.ind.{u} (x : τ) (w : σ) (C : σ → Prop)
        //  : P x w → (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        //
        let CmdInductive {
            name,
            local_types,
            params,
            target_ty,
            mut ctors,
        } = cmd;
        if self.has_const(name) {
            bail!("already defined");
        }
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
        for i in 0..params.len() {
            for j in i + 1..params.len() {
                if params[i].0 == params[j].0 {
                    bail!("duplicate parameters");
                }
            }
            self.proof_env
                .tt_env
                .check_kind(&local_env, &params[i].1, &Kind::base())?;
            local_env.locals.push((params[i].0, params[i].1.clone()));
        }
        self.proof_env
            .tt_env
            .check_kind(&local_env, &target_ty, &Kind::base())?;
        if target_ty.target() != &mk_type_prop() {
            bail!("the target type of an inductive predicate must be Prop");
        }
        for i in 0..ctors.len() {
            for j in i + 1..ctors.len() {
                if ctors[i].name == ctors[j].name {
                    bail!("duplicate constructors");
                }
            }
        }
        local_env.locals.insert(0, (name, target_ty.clone()));
        let mut ctor_args_list = vec![];
        let mut ctor_target_list = vec![];
        let mut ctor_ind_args_list = vec![];
        for ctor in &mut ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            if self.has_axiom(ctor_name) {
                bail!("already defined");
            }
            for i in 0..ctor.params.len() {
                for j in i + 1..ctor.params.len() {
                    if ctor.params[i].0 == ctor.params[j].0 {
                        bail!("duplicate parameters");
                    }
                }
                self.proof_env
                    .tt_env
                    .check_kind(&local_env, &ctor.params[i].1, &Kind::base())?;
                local_env
                    .locals
                    .push((ctor.params[i].0, ctor.params[i].1.clone()));
            }
            self.proof_env.tt_env.check_type(
                &mut local_env,
                &mut ctor.target,
                &mut mk_type_prop(),
            )?;
            local_env
                .locals
                .truncate(local_env.locals.len() - ctor.params.len());

            let mut m = ctor.target.clone();
            let mut ctor_args = vec![];
            while let Ok(imp) = Imp::try_from(m.clone()) {
                ctor_args.push(imp.lhs);
                m = imp.rhs;
            }
            ctor_args_list.push(ctor_args.clone());
            if m.head() != &mk_local(name) {
                if Forall::try_from(m.clone()).is_ok() {
                    bail!("currently only universal quantification in the left most is supported");
                }
                bail!("invalid constructor: {m}");
            }
            for a in m.args() {
                if a.contains_local(&name) {
                    bail!("invalid target");
                }
            }
            ctor_target_list.push(m);
            let mut ctor_ind_args = vec![];
            for ctor_arg in &ctor_args {
                let mut m = ctor_arg.clone();
                loop {
                    if let Ok(forall) = Forall::try_from(m.clone()) {
                        let name = Name::fresh();
                        m = forall.body;
                        m.open(&mk_local(name));
                    } else if let Ok(imp) = Imp::try_from(m.clone()) {
                        if imp.lhs.contains_local(&name) {
                            bail!("constructor violates strict positivity");
                        }
                        m = imp.rhs;
                    } else {
                        break;
                    }
                }
                if m.contains_local(&name) {
                    if m.head() != &mk_local(name) {
                        bail!("invalid target");
                    }
                    for a in m.args() {
                        if a.contains_local(&name) {
                            bail!("invalid target");
                        }
                    }
                    ctor_ind_args.push(ctor_arg.clone());
                }
            }
            ctor_ind_args_list.push(ctor_ind_args);
        }
        local_env.locals.remove(0);
        if need_shrink {
            let mut shrinked_local_types = vec![];
            for t in local_env.local_types {
                if params.iter().any(|(_, ty)| ty.contains_local(&t))
                    || target_ty.contains_local(&t)
                    || ctors.iter().any(|ctor| {
                        ctor.params.iter().any(|(_, ty)| ty.contains_local(&t))
                            || ctor.target.contains_local_type(&t)
                    })
                {
                    shrinked_local_types.push(t);
                    continue;
                }
            }
            local_env.local_types = shrinked_local_types;
        }
        let ind_name = Name::intern(&format!("{}.ind", name)).unwrap();
        if self.has_axiom(ind_name) {
            bail!("already defined");
        }
        // well-formedness check is completed.

        // inductive P.{u} (x : τ) : σ → Prop
        // ↦ const P.{u} : τ → σ → Prop
        let mut pred_ty = target_ty.clone();
        let mut param_types = vec![];
        for (_, t) in &params {
            param_types.push(t.clone());
        }
        pred_ty.discharge(param_types);
        self.add_const(name, local_env.local_types.clone(), pred_ty);

        // inductive P.{u} (x : τ) : σ → Prop
        // | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        // ↦ axiom P.intro.{u} (x : τ) : ∀ y, φ → (∀ z, ψ → P.{u} x M) → P.{u} x N
        for ctor in &ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            let mut target = ctor.target.clone();
            // P.{u} x
            let mut stash = mk_const(
                name,
                local_env
                    .local_types
                    .iter()
                    .map(|name| mk_type_local(*name))
                    .collect(),
            );
            stash.apply(params.iter().map(|(name, _)| mk_local(*name)));
            let subst = [(name, &stash)];
            target.subst(&subst);
            for (name, ty) in ctor.params.iter().rev() {
                target.close(*name);
                target = Forall {
                    name: *name,
                    ty: ty.clone(),
                    body: target,
                }
                .into();
            }
            for (name, ty) in params.iter().rev() {
                target.close(*name);
                target = Forall {
                    name: *name,
                    ty: ty.clone(),
                    body: target,
                }
                .into();
            }
            self.add_axiom(
                ctor_name,
                local_env.local_types.clone(),
                params.len() + ctor.params.len(),
                target,
            );
        }

        // inductive P.{u} (x : τ) : σ → Prop
        // | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        // ↦ axiom P.ind.{u} (x : τ) (w : σ) (C : σ → Prop)
        //  : P x w → (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        let indexes = target_ty
            .clone()
            .undischarge()
            .into_iter()
            .map(|t| (Name::fresh(), t))
            .collect::<Vec<_>>();
        let motive = Name::fresh();
        // C w
        let mut target = mk_local(motive);
        target.apply(indexes.iter().map(|(x, _)| mk_local(*x)));
        // (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        for (ctor, (ctor_args, (mut ctor_target, ctor_ind_args))) in zip(
            ctors,
            zip(ctor_args_list, zip(ctor_target_list, ctor_ind_args_list)),
        ) {
            // P ↦ C
            let subst_with_motive = [(name, &mk_local(motive))];

            // C N
            ctor_target.subst(&subst_with_motive);

            // (∀ z, ψ → C M) → C N
            for mut ctor_ind_arg in ctor_ind_args.into_iter().rev() {
                ctor_ind_arg.subst(&subst_with_motive);
                ctor_target = Imp {
                    lhs: ctor_ind_arg,
                    rhs: ctor_target,
                }
                .into();
            }

            // P ↦ P.{u} x
            let mut stash = mk_const(
                name,
                local_env
                    .local_types
                    .iter()
                    .map(|name| mk_type_local(*name))
                    .collect(),
            );
            stash.apply(params.iter().map(|(name, _)| mk_local(*name)));
            let subst = [(name, &stash)];

            // φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N
            for mut ctor_arg in ctor_args.into_iter().rev() {
                ctor_arg.subst(&subst);
                ctor_target = Imp {
                    lhs: ctor_arg,
                    rhs: ctor_target,
                }
                .into();
            }

            // ∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N
            for (x, t) in ctor.params.into_iter().rev() {
                ctor_target.close(x);
                ctor_target = Forall {
                    name: x,
                    ty: t,
                    body: ctor_target,
                }
                .into();
            }

            target = Imp {
                lhs: ctor_target,
                rhs: target,
            }
            .into();
        }
        let mut p = mk_const(
            name,
            local_env
                .local_types
                .iter()
                .map(|name| mk_type_local(*name))
                .collect(),
        );
        p.apply(params.iter().map(|(name, _)| mk_local(*name)));
        p.apply(indexes.iter().map(|(x, _)| mk_local(*x)));
        target = Imp {
            lhs: p,
            rhs: target,
        }
        .into();

        // ∀ (C : σ → Prop), P x w → (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        target.close(motive);
        target = Forall {
            name: Name::intern("motive").unwrap(),
            ty: target_ty.clone(),
            body: target,
        }
        .into();
        // ∀ w y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N
        for (x, t) in indexes.iter().rev() {
            target.close(*x);
            target = Forall {
                name: *x,
                ty: t.clone(),
                body: target,
            }
            .into();
        }
        // ∀ x w y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N
        for (x, t) in params.iter().rev() {
            target.close(*x);
            target = Forall {
                name: *x,
                ty: t.clone(),
                body: target,
            }
            .into();
        }
        self.add_axiom(
            ind_name,
            local_env.local_types,
            params.len() + indexes.len() + 1,
            target,
        );
        Ok(())
    }
}
