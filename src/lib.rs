use anyhow::Context;
use lex::Lex;
use parse::{ParseError, Parser};
use print::Pretty;
use proof::Axiom;
use tt::{Const, Name};

mod cmd;
mod elab;
mod expr;
mod lex;
mod parse;
mod print;
mod proof;
mod tt;

fn print_const(eval: &cmd::Eval, name: Name) {
    let Const {
        local_types,
        local_classes,
        ty,
    } = eval.const_table.get(&name).unwrap();
    print!("const {}.{{", name);
    let mut first = true;
    for local_type in local_types {
        if !first {
            print!(", ");
        }
        print!("{}", local_type);
        first = false;
    }
    print!("}}");
    for local_class in local_classes {
        println!(" [{}]", Pretty::new(&eval.pp, local_class));
    }
    println!(": {}", Pretty::new(&eval.pp, ty));
}

fn print_axiom(eval: &cmd::Eval, name: Name) {
    let Axiom {
        local_types,
        local_classes,
        target,
    } = eval.axiom_table.get(&name).unwrap();
    print!("axiom {}.{{", name);
    let mut first = true;
    for local_type in local_types {
        if !first {
            print!(", ");
        }
        print!("{}", local_type);
        first = false;
    }
    print!("}}");
    for local_class in local_classes {
        print!(" [{}]", Pretty::new(&eval.pp, local_class));
    }
    println!(": {}", Pretty::new(&eval.pp, target));
}

pub fn process(input: &str) -> anyhow::Result<()> {
    let mut eval = cmd::Eval::default();

    let mut lex = Lex::new(input);

    loop {
        let cmd =
            match Parser::new(&mut lex, &eval.tt, &eval.ns, eval.local_type_consts.clone()).cmd() {
                Ok(cmd) => cmd,
                Err(ParseError::Eof { .. }) => {
                    break;
                }
                Err(e) => {
                    return Err(e).context("parse error");
                }
            };
        eval.run_cmd(cmd.clone()).context("command error")?;
        match cmd {
            cmd::Cmd::Def(cmd) => {
                println!("def {}", cmd.name);
                print_const(&eval, cmd.name);
            }
            cmd::Cmd::Lemma(cmd) => {
                println!("lemma {}", cmd.name);
                print_axiom(&eval, cmd.name);
            }
            cmd::Cmd::Axiom(cmd) => {
                println!("axiom {}", cmd.name);
                print_axiom(&eval, cmd.name);
            }
            cmd::Cmd::TypeInductive(cmd) => {
                println!("type inductive {}", cmd.name);
                for ctor in &cmd.ctors {
                    let ctor_name = Name::intern(&format!("{}.{}", cmd.name, ctor.name)).unwrap();
                    print_const(&eval, ctor_name);
                }
                let ind_name = Name::intern(&format!("{}.ind", cmd.name)).unwrap();
                print_axiom(&eval, ind_name);

                let rec_name = Name::intern(&format!("{}.rec", cmd.name)).unwrap();
                print_const(&eval, rec_name);

                for ctor in &cmd.ctors {
                    let ctor_spec_name =
                        Name::intern(&format!("{}.{}.spec", cmd.name, ctor.name)).unwrap();
                    print_axiom(&eval, ctor_spec_name);
                }
            }
            cmd::Cmd::Inductive(cmd) => {
                println!("inductive {}", cmd.name);
                print_const(&eval, cmd.name);
                for ctor in &cmd.ctors {
                    let ctor_name = Name::intern(&format!("{}.{}", cmd.name, ctor.name)).unwrap();
                    print_axiom(&eval, ctor_name);
                }
                let ind_name = Name::intern(&format!("{}.ind", cmd.name)).unwrap();
                print_axiom(&eval, ind_name);
            }
            cmd::Cmd::Structure(cmd) => {
                println!("structure {}", cmd.name);
                for field in &cmd.fields {
                    match field {
                        cmd::StructureField::Const(field) => {
                            let field_name =
                                Name::intern(&format!("{}.{}", cmd.name, field.name)).unwrap();
                            print_const(&eval, field_name);
                        }
                        cmd::StructureField::Axiom(field) => {
                            let field_name =
                                Name::intern(&format!("{}.{}", cmd.name, field.name)).unwrap();
                            print_axiom(&eval, field_name);
                        }
                    }
                }
                let abs_name = Name::intern(&format!("{}.abs", cmd.name)).unwrap();
                print_axiom(&eval, abs_name);
                let ext_name = Name::intern(&format!("{}.ext", cmd.name)).unwrap();
                print_axiom(&eval, ext_name);
            }
            cmd::Cmd::Instance(cmd) => {
                println!("instance {}", cmd.name);
                print_const(&eval, cmd.name);
                for field in &cmd.fields {
                    match field {
                        cmd::InstanceField::Def(field) => {
                            let field_name =
                                Name::intern(&format!("{}.{}", cmd.name, field.name)).unwrap();
                            print_const(&eval, field_name);
                        }
                        cmd::InstanceField::Lemma(field) => {
                            let field_name =
                                Name::intern(&format!("{}.{}", cmd.name, field.name)).unwrap();
                            print_axiom(&eval, field_name);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    Ok(())
}
