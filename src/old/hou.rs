// /// A convenient representation of head normal form.
// /// Recall that every (normal) term has form `λv*. m n*`.
// #[derive(Clone)]
// struct Triple {
//     /// Outermost-first
//     binder: Vec<(Name, Type)>,
//     /// Fvar, Const, or Mvar.
//     // TODO: use locally nameless forms directly.
//     head: Term,
//     /// Huch calls these parts "arguments" [Huch, 2020](https://www21.in.tum.de/teaching/sar/SS20/5.pdf).
//     /// See also Notation 2.29 in The Clausal Theory of Types [Wolfram, 2009].
//     args: Vec<Term>,
// }

// impl From<Term> for Triple {
//     fn from(mut m: Term) -> Self {
//         assert!(m.is_canonical());
//         let binder = m.unabstract();
//         let args = m.uncurry();
//         let head = m;
//         Self { binder, head, args }
//     }
// }

// impl From<Triple> for Term {
//     fn from(m: Triple) -> Self {
//         let Triple { binder, head, args } = m;
//         let mut m = head;
//         m.curry(args);
//         m.r#abstract(binder);
//         m
//     }
// }

// impl Triple {
//     /// See [Vukmirović+, 2020].
//     pub fn is_flex(&self) -> bool {
//         match self.head {
//             Term::Mvar(_, _) => true,
//             Term::Bvar(_, _) | Term::Fvar(_, _) | Term::Const(_, _) => false,
//             Term::Abs(_, _) | Term::App(_, _) => unreachable!(),
//         }
//     }

//     /// See [Vukmirović+, 2020].
//     pub fn is_rigid(&self) -> bool {
//         !self.is_flex()
//     }

//     /// Suppose `f ≡ λx*. X t*` and `r ≡ λy*. x u*`.
//     /// Imitation: X ↦ λz*. x (Y z*)* (when x = c)
//     /// Projection: X ↦ λz*. zᵢ (Y z*)* (when τ(zᵢ) is compatible with τ(x))
//     fn r#match(&self, other: &Triple) -> Vec<(MvarId, Term)> {
//         assert!(self.is_flex());
//         assert!(self.is_rigid());
//         let (t, mid) = if let Term::Mvar(t, mid) = &self.head {
//             (t, *mid)
//         } else {
//             panic!("self is not flex")
//         };
//         let binder: Vec<_> = t
//             .components()
//             .into_iter()
//             .map(|t| (Name::fresh(), t.clone()))
//             .collect();
//         let mut heads = vec![];
//         // projection
//         for (x, u) in &binder {
//             if t.target() == u.target() {
//                 heads.push(Term::Fvar((*u).clone(), x.to_owned()));
//             }
//         }
//         // imitation
//         match other.head {
//             Term::Fvar(_, _) | Term::Const(_, _) => {
//                 heads.push(other.head.clone());
//             }
//             _ => {}
//         };
//         let mut subst = vec![];
//         for mut head in heads {
//             head.curry(
//                 head.r#type()
//                     .components()
//                     .into_iter()
//                     .map(|t| {
//                         let mut t = t.clone();
//                         t.curry(binder.iter().map(|(_, t)| (*t).clone()).collect());
//                         let mut m = Term::Mvar(t, MvarId::fresh());
//                         m.curry(
//                             binder
//                                 .iter()
//                                 .map(|(x, t)| Term::Fvar(t.clone(), x.to_owned()))
//                                 .collect(),
//                         );
//                         m
//                     })
//                     .collect(),
//             );
//             head.r#abstract(binder.clone());
//             subst.push((mid, head));
//         }
//         subst
//     }
// }

// /// In Huet's original paper a disagreement set is just a finite set of pairs of terms.
// /// For performance improvement, we classify pairs into rigid/rigid, flex/rigid, and flex/flex
// /// at the preprocessing phase.
// #[derive(Default)]
// struct DisagreementSet {
//     // rigid-rigid
//     rr: Vec<(Triple, Triple)>,
//     // flex-rigid
//     fr: Vec<(Triple, Triple)>,
//     // flex-flex
//     ff: Vec<(Triple, Triple)>,
// }

// impl DisagreementSet {
//     fn add(&mut self, m1: Triple, m2: Triple) {
//         match (m1.is_rigid(), m2.is_rigid()) {
//             (true, true) => self.rr.push((m1, m2)),
//             (true, false) => self.fr.push((m2, m1)),
//             (false, true) => self.fr.push((m1, m2)),
//             (false, false) => self.ff.push((m1, m2)),
//         }
//     }

//     /// decompose rigid-rigid pairs by chopping into smaller ones
//     fn simplify(&mut self) -> bool {
//         while let Some((h1, h2)) = self.rr.pop() {
//             assert_eq!(h1.binder.len(), h2.binder.len());
//             let has_same_heading = {
//                 let mut head2 = h2.head.clone();
//                 for ((x, t1), (y, t2)) in h1.binder.iter().zip(h2.binder.iter()) {
//                     assert_eq!(t1, t2);
//                     let m = Term::Fvar(t1.clone(), x.to_owned());
//                     head2.subst(y, &m);
//                 }
//                 h1.head == head2
//             };
//             if has_same_heading {
//                 assert_eq!(h1.args.len(), h2.args.len());
//                 for (mut a1, mut a2) in h1.args.into_iter().zip(h2.args.into_iter()) {
//                     a1.r#abstract(h1.binder.clone());
//                     a2.r#abstract(h2.binder.clone());
//                     self.add(Triple::from(a1), Triple::from(a2));
//                 }
//             } else {
//                 return false;
//             }
//         }
//         true
//     }

//     fn solve(self) -> Vec<(MvarId, Term)> {
//         let mut queue = VecDeque::new();
//         queue.push_back((self, vec![]));
//         while let Some((mut set, subst)) = queue.pop_front() {
//             if !set.simplify() {
//                 continue;
//             }
//             if set.fr.is_empty() {
//                 return subst;
//             }
//             let (h1, h2) = &set.fr[0];
//             for (mid, m) in h1.r#match(h2) {
//                 let mut new_set = DisagreementSet::default();
//                 for (m1, m2) in set.fr.iter().chain(set.ff.iter()) {
//                     let mut m1 = Term::from(m1.clone());
//                     m1.instantiate(mid, &m);
//                     m1.canonicalize();
//                     let mut m2 = Term::from(m2.clone());
//                     m2.instantiate(mid, &m);
//                     m2.canonicalize();
//                     new_set.add(Triple::from(m1), Triple::from(m2));
//                 }
//                 let mut new_subst = subst.clone();
//                 new_subst.push((mid, m));
//                 queue.push_back((new_set, new_subst));
//             }
//         }
//         todo!("no solution found");
//     }
// }

// impl Term {
//     /// `self` and `other` must be type-correct and type-equal under the same environment.
//     pub fn unify(&mut self, other: &mut Term) {
//         assert_eq!(self.r#type(), other.r#type());
//         let mut set = DisagreementSet::default();
//         self.canonicalize();
//         let h1 = Triple::from(self.clone());
//         other.canonicalize();
//         let h2 = Triple::from(mem::take(other));
//         set.add(h1, h2);
//         let subst = set.solve();
//         for (mid, m) in subst {
//             self.instantiate(mid, &m);
//         }
//         *other = self.clone();
//     }
// }
