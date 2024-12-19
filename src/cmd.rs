use std::iter::zip;

use anyhow::bail;

use crate::{
    expr::{self, mk_expr_app, mk_expr_assume, mk_expr_assump, Expr},
    parse::{FactInfo, Nasmespace, TokenTable},
    print::OpTable,
    proof::{self, mk_type_prop, Forall, Imp},
    tt::{
        mk_app, mk_const, mk_local, mk_type_arrow, mk_type_const, mk_type_local, Def, Kind,
        LocalEnv, Name, Term, Type,
    },
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
    LocalTypeConst(CmdLocalTypeConst),
    TypeInductive(CmdTypeInductive),
    Inductive(CmdInductive),
    Structure(CmdStructure),
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
    pub local_types: Vec<Name>,
    pub ty: Type,
    pub target: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdAxiom {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub target: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdLemma {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub target: Term,
    pub holes: Vec<(Name, Type)>,
    pub expr: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdConst {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdTypeConst {
    pub name: Name,
    pub kind: Kind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdLocalTypeConst {
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
    pub local_types: Vec<Name>,
    pub params: Vec<(Name, Type)>,
    pub target_ty: Type,
    pub ctors: Vec<Constructor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constructor {
    pub name: Name,
    pub target: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdStructure {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub fields: Vec<StructureField>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StructureField {
    Const(StructureConst),
    Axiom(StructureAxiom),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructureConst {
    pub name: Name,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructureAxiom {
    pub name: Name,
    pub target: Term,
}

#[derive(Debug, Clone, Default)]
pub struct Eval {
    pub proof_env: proof::Env,
    pub tt: TokenTable,
    pub ns: Nasmespace,
    pub pp: OpTable,
    pub local_type_consts: Vec<Name>,
}

impl Eval {
    fn add_const(&mut self, name: Name, local_types: Vec<Name>, ty: Type) {
        self.ns.consts.insert(name, local_types.len());
        self.proof_env.tt_env.consts.insert(name, (local_types, ty));
    }

    fn add_axiom(&mut self, name: Name, local_types: Vec<Name>, target: Term) {
        let mut num_params = 0;
        {
            let mut target = target.clone();
            while let Ok(forall) = Forall::try_from(target) {
                num_params += 1;
                target = forall.body;
            }
        }
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
                    mut local_types,
                    mut ty,
                    mut target,
                } = inner;
                if self.has_const(name) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !ty.contains_local(local_type_const) {
                        // unused
                        continue;
                    }
                    local_types.insert(0, *local_type_const);
                }
                let mut local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes: vec![],
                };
                self.proof_env
                    .tt_env
                    .check_type(&mut local_env, &mut target, &mut ty)?;
                self.add_const(name, local_env.local_types.clone(), ty.clone());
                self.proof_env.tt_env.defs.insert(
                    name,
                    Def {
                        local_types: local_env.local_types,
                        ty,
                        target,
                        hint: self.proof_env.tt_env.defs.len(),
                    },
                );
                Ok(())
            }
            Cmd::Axiom(inner) => {
                let CmdAxiom {
                    name,
                    mut local_types,
                    mut target,
                } = inner;
                if self.has_axiom(name) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !target.contains_local_type(local_type_const) {
                        // unused
                        continue;
                    }
                    local_types.insert(0, *local_type_const);
                }
                let mut local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes: vec![],
                };
                self.proof_env.tt_env.check_type(
                    &mut local_env,
                    &mut target,
                    &mut mk_type_prop(),
                )?;
                self.add_axiom(name, local_env.local_types, target);
                Ok(())
            }
            Cmd::Lemma(inner) => {
                let CmdLemma {
                    name,
                    mut local_types,
                    mut target,
                    holes,
                    expr,
                } = inner;
                if self.has_axiom(name) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !target.contains_local_type(local_type_const) {
                        // unused
                        continue;
                    }
                    local_types.insert(0, *local_type_const);
                }
                let mut local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes,
                };
                self.proof_env.tt_env.check_type(
                    &mut local_env,
                    &mut target,
                    &mut mk_type_prop(),
                )?;
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
                self.add_axiom(name, local_env.local_types, target);
                Ok(())
            }
            Cmd::Const(inner) => {
                let CmdConst {
                    name,
                    mut local_types,
                    ty,
                } = inner;
                if self.has_const(name) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !ty.contains_local(local_type_const) {
                        // unused
                        continue;
                    }
                    local_types.insert(0, *local_type_const);
                }
                let local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes: vec![],
                };
                self.proof_env
                    .tt_env
                    .check_kind(&local_env, &ty, &Kind::base())?;
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
            Cmd::LocalTypeConst(inner) => {
                let CmdLocalTypeConst { variables } = inner;
                for i in 0..variables.len() {
                    for j in i + 1..variables.len() {
                        if variables[i] == variables[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for v in &variables {
                    if self.local_type_consts.contains(v) {
                        bail!("type variable already defined");
                    }
                }
                self.local_type_consts.extend(variables);
                Ok(())
            }
            Cmd::TypeInductive(cmd) => self.run_type_inductive_cmd(cmd),
            Cmd::Inductive(cmd) => self.run_inductive_cmd(cmd),
            Cmd::Structure(cmd) => self.run_structure_cmd(cmd),
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
            let ctor_spec_name = Name::intern(&format!("{}.spec", ctor_name)).unwrap();
            if self.has_const(ctor_spec_name) {
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
        self.add_axiom(ind_name, local_types.clone(), target);

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
        self.add_const(rec_name, rec_local_types.clone(), rec_ty);

        let rhs_binders = cont_params
            .into_iter()
            .zip(cont_param_tys)
            .map(|(x, t)| (x, x, t))
            .collect::<Vec<_>>();
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

            let mut spec = mk_const(Name::intern("eq").unwrap(), vec![mk_type_local(rec_ty_var)]);
            spec.apply([lhs, rhs]);

            for (x, t) in ctor_params.into_iter().rev() {
                spec.abs(&[(x, x, t.clone())], true);
                let mut m = mk_const(Name::intern("forall").unwrap(), vec![t]);
                m.apply([spec]);
                spec = m;
            }

            let ctor_spec_name = Name::intern(&format!("{}.spec", ctor_name)).unwrap();
            self.add_axiom(ctor_spec_name, rec_local_types.clone(), spec);
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
            mut local_types,
            params,
            target_ty,
            mut ctors,
        } = cmd;
        if self.has_const(name) {
            bail!("already defined");
        }
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i] == local_types[j] {
                    bail!("duplicate type variables");
                }
            }
        }
        for local_type_const in self.local_type_consts.iter().rev() {
            if local_types.contains(local_type_const) {
                // shadowed by the .{} binder
                continue;
            }
            if params
                .iter()
                .any(|(_, ty)| ty.contains_local(local_type_const))
                || target_ty.contains_local(local_type_const)
                || ctors
                    .iter()
                    .any(|ctor| ctor.target.contains_local_type(local_type_const))
            {
                local_types.insert(0, *local_type_const);
            }
        }
        let mut local_env = LocalEnv {
            local_types,
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
        let mut ctor_params_list = vec![];
        let mut ctor_args_list = vec![];
        let mut ctor_target_list = vec![];
        let mut ctor_ind_args_list = vec![];
        for ctor in &mut ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            if self.has_axiom(ctor_name) {
                bail!("already defined");
            }
            self.proof_env.tt_env.check_type(
                &mut local_env,
                &mut ctor.target,
                &mut mk_type_prop(),
            )?;

            let mut m = ctor.target.clone();
            let mut ctor_params = vec![];
            while let Ok(mut forall) = Forall::try_from(m.clone()) {
                let fresh_name = Name::fresh();
                ctor_params.push((fresh_name, forall.name, forall.ty));
                forall.body.open(&mk_local(fresh_name));
                m = forall.body;
            }
            ctor_params_list.push(ctor_params);
            let mut ctor_args = vec![];
            while let Ok(imp) = Imp::try_from(m.clone()) {
                ctor_args.push(imp.lhs);
                m = imp.rhs;
            }
            ctor_args_list.push(ctor_args.clone());
            if m.head() != &mk_local(name) {
                bail!("invalid constructor. Currently only Horn clauses are supported in inductive clauses: {m}");
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
            for (name, ty) in params.iter().rev() {
                target.close(*name);
                target = Forall {
                    name: *name,
                    ty: ty.clone(),
                    body: target,
                }
                .into();
            }
            self.add_axiom(ctor_name, local_env.local_types.clone(), target);
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
        let mut guards = vec![];
        // (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        for (ctor_params, (ctor_args, (ctor_target, ctor_ind_args))) in zip(
            ctor_params_list,
            zip(ctor_args_list, zip(ctor_target_list, ctor_ind_args_list)),
        ) {
            // P ↦ C
            let subst_with_motive = [(name, &mk_local(motive))];

            let mut guard = ctor_target;

            // C N
            guard.subst(&subst_with_motive);

            // (∀ z, ψ → C M) → C N
            for mut ctor_ind_arg in ctor_ind_args.into_iter().rev() {
                ctor_ind_arg.subst(&subst_with_motive);
                guard = Imp {
                    lhs: ctor_ind_arg,
                    rhs: guard,
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
                guard = Imp {
                    lhs: ctor_arg,
                    rhs: guard,
                }
                .into();
            }

            // ∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N
            for (x, nickname, t) in ctor_params.into_iter().rev() {
                guard.close(x);
                guard = Forall {
                    name: nickname,
                    ty: t,
                    body: guard,
                }
                .into();
            }

            guards.push(guard);
        }
        for guard in guards.into_iter().rev() {
            target = Imp {
                lhs: guard,
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
        self.add_axiom(ind_name, local_env.local_types, target);
        Ok(())
    }

    fn run_structure_cmd(&mut self, cmd: CmdStructure) -> anyhow::Result<()> {
        // Use the inhab type as a prototypical example:
        //
        // structure inhab u := {
        //  const rep : set u
        //  axiom inhabited : ∃ x, x ∈ rep
        // }
        let CmdStructure {
            name,
            local_types,
            mut fields,
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
        let mut const_field_names = vec![];
        let mut axiom_field_names = vec![];
        for field in &mut fields {
            match field {
                StructureField::Const(field) => {
                    let StructureConst {
                        name: field_name,
                        ty: field_ty,
                    } = &*field;
                    let fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    if self.has_const(fullname) {
                        bail!("already defined");
                    }
                    if const_field_names.contains(&field_name) {
                        bail!("duplicate const field");
                    }
                    const_field_names.push(field_name);
                    self.proof_env
                        .tt_env
                        .check_kind(&local_env, field_ty, &Kind::base())?;
                    local_env.locals.push((*field_name, field_ty.clone()));
                }
                StructureField::Axiom(field) => {
                    let StructureAxiom {
                        name: ref field_name,
                        target,
                    } = field;
                    let fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    if self.has_axiom(fullname) {
                        bail!("already defined");
                    }
                    if axiom_field_names.contains(&field_name) {
                        bail!("duplicate axiom field");
                    }
                    axiom_field_names.push(field_name);
                    self.proof_env.tt_env.check_type(
                        &mut local_env,
                        target,
                        &mut mk_type_prop(),
                    )?;
                }
            }
        }
        let abs_name = Name::intern(&format!("{}.abs", name)).unwrap();
        if self.has_axiom(abs_name) {
            bail!("already defined");
        }
        let ext_name = Name::intern(&format!("{}.ext", name)).unwrap();
        if self.has_axiom(ext_name) {
            bail!("already defined");
        }
        // well-formedness check is completed.
        self.add_type_const(name, Kind(local_types.len()));
        let instance = Name::fresh();
        let instance_ty = {
            let mut ty = mk_type_const(name);
            ty.apply(local_types.iter().map(|x| mk_type_local(*x)));
            ty
        };
        let mut subst = vec![];
        for field in &fields {
            match field {
                StructureField::Const(field) => {
                    // rep : set u
                    // ↦ inhab.rep.{u} : inhab u → set u
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();
                    let mut ty = field.ty.clone();
                    ty.discharge([instance_ty.clone()]);
                    self.add_const(fullname, local_types.clone(), ty);

                    // rep ↦ inhab.rep.{u} d
                    let mut target = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                    );
                    target.apply([mk_local(instance)]);
                    subst.push((field.name, target));
                }
                StructureField::Axiom(field) => {
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();

                    let mut target = field.target.clone();
                    target.subst(&subst.iter().map(|(x, m)| (*x, m)).collect::<Vec<_>>());

                    target.abs(
                        &[(instance, "d".try_into().unwrap(), instance_ty.clone())],
                        true,
                    );
                    target = mk_app(
                        mk_const(Name::try_from("forall").unwrap(), vec![instance_ty.clone()]),
                        target,
                    );

                    self.add_axiom(fullname, local_types.clone(), target);
                }
            }
        }
        // generate abstraction principle
        // axiom inhab.abs.{u} (s : set u) : (∃ x, x ∈ s) → ∃ d, s = inhab.rep d
        let mut params = vec![];
        let mut guards = vec![];
        let mut chars = vec![];
        let mut subst = vec![];
        for field in &fields {
            match field {
                StructureField::Const(field) => {
                    // (s : set u)
                    let param = Name::fresh();
                    params.push((param, field.ty.clone()));

                    // inhab.rep d
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();
                    let mut rhs = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                    );
                    rhs.apply([mk_local(instance)]);

                    // s = inhab.rep d
                    let mut char = mk_const(Name::intern("eq").unwrap(), vec![field.ty.clone()]);
                    char.apply([mk_local(param), rhs]);
                    chars.push(char);

                    // rep ↦ s
                    subst.push((field.name, mk_local(param)));
                }
                StructureField::Axiom(field) => {
                    let mut target = field.target.clone();
                    target.subst(&subst.iter().map(|(x, m)| (*x, m)).collect::<Vec<_>>());

                    guards.push(target);
                }
            }
        }
        let mut abs = mk_const(Name::intern("exists").unwrap(), vec![instance_ty.clone()]);
        abs.apply([{
            let mut char = chars
                .into_iter()
                .reduce(|left, right| {
                    let mut conj = mk_const(Name::intern("and").unwrap(), vec![]);
                    conj.apply([left, right]);
                    conj
                })
                .unwrap_or_else(|| mk_const(Name::intern("true").unwrap(), vec![]));
            char.abs(
                &[(instance, "d".try_into().unwrap(), instance_ty.clone())],
                true,
            );
            char
        }]);
        for guard in guards.into_iter().rev() {
            abs = Imp {
                lhs: guard,
                rhs: abs,
            }
            .into();
        }
        for (var, ty) in params.iter().rev() {
            abs.abs(&[(*var, *var, ty.clone())], true);
            abs = mk_app(
                mk_const(Name::try_from("forall").unwrap(), vec![ty.clone()]),
                abs,
            );
        }
        self.add_axiom(abs_name, local_types.clone(), abs);

        // generate extensionality
        // axiom inhab.ext.{u} (d₁ d₂ : inhab u) : inhab.rep d₁ = inhab.rep d₂ → d₁ = d₂
        let instance2 = Name::fresh();
        let mut guards = vec![];
        for field in &fields {
            match field {
                StructureField::Const(field) => {
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();
                    let proj = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                    );

                    let mut lhs = proj.clone();
                    lhs.apply([mk_local(instance)]);
                    let mut rhs = proj;
                    rhs.apply([mk_local(instance2)]);

                    let mut guard = mk_const(Name::intern("eq").unwrap(), vec![field.ty.clone()]);
                    guard.apply([lhs, rhs]);
                    guards.push(guard);
                }
                StructureField::Axiom(_) => {}
            }
        }
        let mut target = mk_const(Name::intern("eq").unwrap(), vec![instance_ty.clone()]);
        target.apply([mk_local(instance), mk_local(instance2)]);
        for guard in guards.into_iter().rev() {
            target = Imp {
                lhs: guard,
                rhs: target,
            }
            .into();
        }
        target.abs(
            &[(instance2, "d₂".try_into().unwrap(), instance_ty.clone())],
            true,
        );
        target = mk_app(
            mk_const(Name::try_from("forall").unwrap(), vec![instance_ty.clone()]),
            target,
        );
        target.abs(
            &[(instance, "d₁".try_into().unwrap(), instance_ty.clone())],
            true,
        );
        target = mk_app(
            mk_const(Name::try_from("forall").unwrap(), vec![instance_ty.clone()]),
            target,
        );
        self.add_axiom(ext_name, local_types.clone(), target);
        Ok(())
    }
}
