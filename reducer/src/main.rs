use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::Read;
use std::process;

use pretty::{BoxDoc, Doc};
use proc_macro2::{LineColumn, Span};
use syn::*;
use syn::spanned::Spanned;

const FNS: [&'static str; 3] = ["Fn", "FnOnce", "FnMut"];
const NUMS: [&'static str; 5] = ["u32", "u8", "usize", "isize", "i32"];
const MACROS: [&'static str; 4] = ["abort", "panic", "unimplemented", "unreachable"];

type PP = Doc<'static, BoxDoc<'static, ()>>;

enum ResolutionType { FunName, StructName, TypeVar }

#[derive(Clone)]
struct CompilerState {
    function_substs: HashMap<String, PP>,
}

impl CompilerState {
    fn new() -> CompilerState {
        CompilerState {
            function_substs: HashMap::new(),
        }
    }

    fn add_function_subst(&mut self, ident: Ident, bound: TraitBound) {
        self.function_substs.insert(
            format!("{}", ident),
            fun_bound_to_fun_ty(self.clone(), ident, bound)
        );
    }
}

static mut LAST_SYM: u64 = 0;

fn gensym() -> PP {
    unsafe { LAST_SYM += 1 };
    Doc::text(format!("\"p{}\"", unsafe { LAST_SYM }))
}

fn main() {
    let mut args = env::args();
    let _ = args.next(); // executable name

    let filename = match (args.next(), args.next()) {
        (Some(filename), None) => filename,
        _ => {
            eprintln!("Usage: reducer path/to/filename.rs");
            process::exit(1);
        }
    };

    let mut file = File::open(&filename).expect("Unable to open file");

    let mut src = String::new();
    file.read_to_string(&mut src).expect("Unable to read file");

    let syntax = syn::parse_file(&src).expect("Unable to parse file");

    let init_state = CompilerState::new();
    let docs = syntax.items.into_iter().map(|item| parenthesize(item.to_doc(init_state.clone())));

    let global_env = Doc::text("[")
        .append(Doc::intersperse(docs, Doc::text(";").append(Doc::space())).nest(2))
        .append(Doc::text("]"))
        .group();

    let program =
        Doc::text("let")
        .append(Doc::space())
        .append(Doc::text("sigma"))
        .append(Doc::space())
        .append(Doc::text(":"))
        .append(Doc::space())
        .append(Doc::text("global_env"))
        .append(Doc::space())
        .append(Doc::text("="))
        .group()
        .append(Doc::space())
        .append(global_env)
        .nest(2)
        .group();

    let driver : PP =
        Doc::text("let")
        .append(Doc::space())
        .append(Doc::text("main"))
        .append(Doc::space())
        .append(Doc::text("="))
        .append(Doc::space())
        .append(Doc::text("match"))
        .append(Doc::space())
        .append(Doc::text("wf_global_env"))
        .append(Doc::space())
        .append(Doc::text("sigma"))
        .append(Doc::space())
        .append(Doc::text("with"))
        .nest(2)
        .group()
        .append(Doc::newline())
        .append(
            Doc::text("|")
                .append(Doc::space())
                .append(Doc::text("Succ"))
                .append(Doc::space())
                .append(Doc::text("()"))
                .append(Doc::space())
                .append(Doc::text("->"))
                .append(Doc::space())
                .append(Doc::text("Format.printf"))
                .append(Doc::space())
                .append(Doc::text("\"valid global environment:@. %a@.\""))
                .append(Doc::space())
                .append(Doc::text("pp_global_env"))
                .append(Doc::space())
                .append(Doc::text("sigma"))
                .group()
        )
        .append(Doc::newline())
        .append(
            Doc::text("|")
                .append(Doc::space())
                .append(Doc::text("Fail"))
                .append(Doc::space())
                .append(Doc::text("err"))
                .append(Doc::space())
                .append(Doc::text("->"))
                .group()
                .append(Doc::space())
                .append(
                    Doc::text("Format.printf")
                        .append(Doc::space())
                        .append(Doc::text("\"error: %a@.invalid global environment:@. %a@.\""))
                        .group()
                )
                .append(
                    Doc::space()
                        .append(
                            Doc::text("pp_tc_error")
                                .append(Doc::space())
                                .append(Doc::text("err"))
                                .group()
                        )
                        .append(Doc::space())
                        .append(
                            Doc::text("pp_global_env")
                                .append(Doc::space())
                                .append(Doc::text("sigma"))
                                .group()
                        )
                        .nest(2)
                        .group()
                )
                .nest(2)
                .group()
        )
        .nest(2)
        .group();

    let whole_program =
        Doc::text("open Oxide.Edsl")
        .append(Doc::newline())
        .append(Doc::text("open Oxide.Typeck"))
        .append(Doc::newline())
        .append(Doc::text("open Oxide.Syntax"))
        .append(Doc::newline())
        .append(Doc::newline())
        .append(program)
        .append(Doc::newline())
        .append(Doc::newline())
        .append(driver);

    let mut buf = Vec::new();
    whole_program.render(100, &mut buf).unwrap();
    println!("{}", String::from_utf8(buf).unwrap());
}

fn parenthesize(doc: PP) -> PP {
    Doc::text("(")
        .append(doc.group())
        .append(Doc::text(")"))
}

fn quote(doc: PP) -> PP {
    Doc::text("\"")
        .append(doc.group())
        .append(Doc::text("\""))
        .group()
}

// This is a bit of a hack, we're handling name resolution with the following heuristics:
//   (1) a lowercase path is a function name
//   (2) an uppercase path is a type variable if the is_type flag is true and the length is 1
//   (3) an uppercase path is otherwise a struct name
fn resolve_name(st: CompilerState, path: Path, is_type: bool) -> (PP, ResolutionType) {
    let last_args1 = path.segments.last().unwrap().arguments.clone();
    let last_args2 = last_args1.clone();
    let name = path.segments.iter().fold(String::new(), |mut acc, seg| {
        acc.push_str("::");
        acc.push_str(&format!("{}", seg.ident));
        acc
    }).split_off(2);

    if name == name.to_lowercase() {
        (Doc::text("Fn")
            .append(Doc::space())
            .append(quote(Doc::text(name)))
            .group(), ResolutionType::FunName)
    } else if is_type && name.len() == 1 {
        match st.function_substs.get(&name) {
            Some(doc) => (doc.clone(), ResolutionType::TypeVar),
            None => (Doc::text("TyVar")
                        .append(Doc::space())
                        .append(quote(Doc::text(name)))
                        .group(), ResolutionType::TypeVar)
        }
    } else {
        (Doc::text(if is_type { "structy" } else { "tupstruct" })
            .append(Doc::space())
            .append(
                quote(Doc::text(name))
                    .append(Doc::space())
                    .append(
                        Doc::text("[")
                            .append(last_args1.to_lifetime_generics_doc(st.clone()))
                            .append(Doc::text("]"))
                            .group()
                    )
                    .append(Doc::space())
                    .append(
                        Doc::text("[")
                            .append(last_args2.to_type_generics_doc(st.clone()))
                            .append(Doc::text("]"))
                            .group()
                    )
            )
            .group(), ResolutionType::StructName)
    }
}

fn copyable_doc(attrs: Vec<Attribute>) -> PP {
    for attr in attrs {
        match attr.parse_meta() {
            Ok(Meta::List(metas)) => {
                for meta in metas.nested.into_iter() {
                    if let NestedMeta::Meta(Meta::Path(ident)) = meta {
                        let empty_ident = Ident::new("unrelated", Span::call_site());
                        if ident.get_ident().unwrap_or(&empty_ident) == "Copy" {
                            return Doc::text("true")
                        }
                    }
                }
            },
            Ok(_) | Err(_) => continue,
        }
    }
    Doc::text("false")
}

fn fun_bound_to_fun_ty(st: CompilerState, env_name: Ident, mut bound: TraitBound) -> PP {
    let segment =
        bound.path.segments.pop().expect("bound path should have one segment").into_value();
    let bound_id = format!("{}", segment.ident);
    if FNS.contains(&&bound_id[..]) {
        if let PathArguments::Parenthesized(arguments) = segment.arguments {
            return parenthesize(
                    Doc::text("Fun")
                    .append(Doc::space())
                    .append(parenthesize(
                        Doc::nil()
                            // environment variables
                            .append(Doc::text("[]"))
                            .append(Doc::text(","))
                            .append(Doc::space())
                            // lifetime variables
                            .append(Doc::text("[]"))
                            .append(Doc::text(","))
                            .append(Doc::space())
                            // type variables
                            .append(Doc::text("[]"))
                            .append(Doc::text(","))
                            .append(Doc::space())
                            // parameter types
                            .append(
                                Doc::text("[")
                                    .append(Doc::intersperse(
                                        arguments.inputs.into_iter().map(|ty| ty.to_doc(st.clone())),
                                        Doc::text(";").append(Doc::space())
                                    ))
                                    .append(Doc::text("]"))
                                    .group()
                            )
                            .append(Doc::text(","))
                            .append(Doc::space())
                            // captured environment
                            .append(
                                Doc::text("EnvVar")
                                    .append(Doc::space())
                                    .append(parenthesize(
                                        Doc::text(if bound_id == "Fn" {"Shared"} else {"Unique"})
                                            .append(Doc::text(","))
                                            .append(Doc::space())
                                            .append(Doc::text(format!("\"{}\"", env_name)))
                                    ))
                            )
                            .append(Doc::text(","))
                            .append(Doc::space())
                            // return type
                            .append(parenthesize(match arguments.output {
                                ReturnType::Default =>
                                    Doc::text("inferred")
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(Doc::text("BaseTy")
                                            .append(Doc::space())
                                            .append(Doc::text("Unit"))
                                    )
                                    .group(),
                                ReturnType::Type(_, ty) => ty.to_doc(st.clone()),
                            }))
                    ))
            )
        }

        panic!("malformed function type bound")
    }

    panic!("reducer does not support non-function trait bounds");
}

trait PrettyPrint {
    fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>>;
}

trait PrettyPrintPlaceExpr {
    fn to_place_expr_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>>;
}

impl PrettyPrint for Item {
  fn to_doc(self, mut st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Item::Fn(mut item) = self {
            let fn_tyvars: Vec<_> = item.sig.generics.type_params()
                .filter(|param| param.bounds.len() == 1)
                .filter(|param| {
                    if let TypeParamBound::Trait(mut bound) =
                        param.bounds
                            .clone()
                            .pop().unwrap()
                            .into_value() {
                        if bound.path.segments.len() == 1 {
                            let bound_id = format!("{}",
                                bound.path.segments.pop().unwrap()
                                        .into_value().ident
                            );
                            FNS.contains(&&bound_id[..])
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                }).collect();

            let bounds = fn_tyvars.iter()
                .map(|param| {
                    (param.ident.clone(), param.bounds.clone().pop().unwrap().into_value())
                })
                .filter(
                    |(_, bound)| if let TypeParamBound::Trait(_) = bound { true } else { false }
                )
                .map(|(ident, bound)| {
                    if let TypeParamBound::Trait(bound) = bound {
                        (ident, bound)
                    } else {
                        unreachable!()
                    }
                });
            for (ident, bound) in bounds {
                st.add_function_subst(ident, bound);
            }

            return Doc::text("fn")
                .append(Doc::space())
                .append(Doc::text(format!("\"{}\"", item.sig.ident)))
                .group()
                // environment variables
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(
                            Doc::intersperse(
                                fn_tyvars.iter().map(|tyvar|
                                    if let TypeParamBound::Trait(mut bound) = tyvar.bounds.clone()
                                                                                   .pop().unwrap()
                                                                                   .into_value() {
                                        let bound_id = format!("{}",
                                            bound.path.segments.pop().unwrap()
                                                    .into_value().ident
                                        );
                                        Doc::text(if bound_id == "Fn" {"Shared"} else {"Unique"})
                                            .append(Doc::text(","))
                                            .append(Doc::space())
                                            .append(Doc::text(format!("\"{}\"", tyvar.ident)))
                                    } else { unreachable!() }),
                                Doc::text(";").append(Doc::space())
                            )
                        )
                        .append(Doc::text("]"))
                        .group()
                )
                // provenance variables
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(
                            Doc::intersperse(
                                item.sig.generics.lifetimes().map(|lft| lft.clone().to_doc(st.clone())),
                                Doc::text(";").append(Doc::space())
                            )
                        )
                        .append(Doc::text("]"))
                        .group()
                )
                // type variables
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(
                            Doc::intersperse(
                                item.sig.generics.type_params()
                                    .filter(|param| param.bounds.is_empty())
                                    .map(|tyvar| {
                                        Doc::text(format!("\"{}\"", tyvar.ident))
                                    }),
                                Doc::text(";").append(Doc::space())
                            )
                        )
                        .append(Doc::text("]"))
                        .group()
                )
                // parameters
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(
                            Doc::intersperse(
                                item.sig.inputs.clone().into_iter().map(|arg| arg.to_doc(st.clone())),
                                Doc::text(";").append(Doc::space())
                            )
                        )
                        .append(Doc::text("]"))
                        .group()
                )
                // return type
                .append(Doc::space())
                .append(parenthesize(match item.sig.output {
                    ReturnType::Default => item.span().to_doc(st.clone())
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(Doc::text("BaseTy")
                                .append(Doc::space())
                                .append(Doc::text("Unit"))
                        )
                        .group(),
                    ReturnType::Type(_, ty) => ty.to_doc(st.clone()),
                }))
                // where bounds (provenances only)
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(Doc::intersperse(
                            item.sig.generics.make_where_clause()
                                .predicates.iter()
                                .map(|pred| pred.clone().to_doc(st.clone())),
                            Doc::text(";").append(Doc::space())
                        ))
                        .append(Doc::text("]"))
                        .group()
                )
                // body
                .append(Doc::space())
                .append(item.block.to_doc(st.clone()).nest(2))
                .nest(2)
        }

        if let Item::Struct(item) = self {
            return match item.fields {
                Fields::Named(fields) => {
                    Doc::text("RecStructDef")
                        .append(parenthesize(
                            copyable_doc(item.attrs)
                                .append(Doc::text(","))
                                .append(Doc::space())
                                .append(quote(Doc::text(format!("{}", item.ident))))
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // provenance variables
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            item.generics.lifetimes().map(|lft| {
                                                lft.clone().to_doc(st.clone())
                                            }),
                                            Doc::text(";").append(Doc::space())
                                        ))
                                        .append(Doc::text("]"))
                                        .group()
                                )
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // type variables
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            item.generics.type_params().map(|tyvar| {
                                                Doc::text(format!("\"{}\"", tyvar.ident))
                                            }),
                                            Doc::text(";").append(Doc::space())
                                        ))
                                        .append(Doc::text("]"))
                                        .group()
                                )
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // fields
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            fields.named.into_iter()
                                                .flat_map(|field| match field.ident {
                                                    Some(ident) => Some(parenthesize(
                                                        quote(Doc::text(format!("{}", ident)))
                                                            .append(Doc::text(","))
                                                            .append(Doc::space())
                                                            .append(field.ty.to_doc(st.clone()))
                                                    )),
                                                    None => None,
                                                }),
                                            Doc::text(";").append(Doc::space())
                                        ))
                                        .append(Doc::text("]"))
                                        .group()
                                )
                        ))
                },

                Fields::Unnamed(fields) => {
                    Doc::text("TupStructDef")
                        .append(parenthesize(
                            copyable_doc(item.attrs)
                                .append(Doc::text(","))
                                .append(Doc::space())
                                .append(quote(Doc::text(format!("{}", item.ident))))
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // provenance variables
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            item.generics.lifetimes().map(|lft| {
                                                lft.clone().to_doc(st.clone())
                                            }),
                                            Doc::text(";").append(Doc::space())
                                        ))
                                        .append(Doc::text("]"))
                                        .group()
                                )
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // type variables
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            item.generics.type_params().map(|tyvar| {
                                                Doc::text(format!("\"{}\"", tyvar.ident))
                                            }),
                                            Doc::text(";").append(Doc::space())
                                        ))
                                        .append(Doc::text("]"))
                                        .group()
                                )
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // fields
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            fields.unnamed.into_iter()
                                                .flat_map(|field| match field.ident {
                                                    Some(_) => None,
                                                    None => Some(field.ty.to_doc(st.clone())),
                                                }),
                                            Doc::text(";").append(Doc::space())
                                        ))
                                        .append(Doc::text("]"))
                                        .group()
                                )
                        ))
                },

                Fields::Unit => {
                    Doc::text("TupStructDef")
                        .append(parenthesize(
                            copyable_doc(item.attrs)
                                .append(Doc::text(","))
                                .append(Doc::space())
                                .append(quote(Doc::text(format!("{}", item.ident))))
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // provenance variables
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            item.generics.lifetimes().map(|lft| {
                                                lft.clone().to_doc(st.clone())
                                            }),
                                            Doc::text(";").append(Doc::space())
                                        ))
                                        .append(Doc::text("]"))
                                        .group()
                                )
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // type variables
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            item.generics.type_params().map(|tyvar| {
                                                Doc::text(format!("\"{}\"", tyvar.ident))
                                            }),
                                            Doc::text(";").append(Doc::space())
                                        ))
                                        .append(Doc::text("]"))
                                        .group()
                                )
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // fields
                                .append(Doc::text("[]"))
                        ))
                },
            }
        }

        println!("{:#?}", self);
        Doc::nil()
    }
}

impl PrettyPrint for Block {
  fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        let mut stmts_backwards = self.stmts.clone().into_iter().rev().peekable();
        let init_acc = if let Some(Stmt::Semi(_, semi)) = stmts_backwards.peek() {
            parenthesize(
                semi.spans[0].to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(Doc::text("Prim"))
                    .append(Doc::space())
                    .append(Doc::text("Unit"))
                    .group()
            )
        } else if let Some(Stmt::Local(stmt)) = stmts_backwards.peek() {
            parenthesize(
                stmt.semi_token.spans[0].to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(Doc::text("Prim"))
                    .append(Doc::space())
                    .append(Doc::text("Unit"))
                    .group()
            )
        } else if let None = stmts_backwards.peek() {
            parenthesize(
                self.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(Doc::text("Prim"))
                    .append(Doc::space())
                    .append(Doc::text("Unit"))
                    .group()
            )
        } else {
            Doc::nil()
        };
        stmts_backwards.fold(init_acc, |acc, stmt| {
            match stmt {
                Stmt::Local(stmt) => parenthesize(
                    stmt.span().to_doc(st.clone())
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(Doc::text("Let"))
                        .append(Doc::space())
                        .append(parenthesize(
                            (if let Pat::Type(stmt) = stmt.pat {
                                if let Pat::Ident(pat) = *stmt.pat {
                                    Doc::text(format!("\"{}\"", pat.ident))
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        .append(stmt.ty.to_doc(st.clone()))
                                } else {
                                    panic!("bindings must use identifiers, not pattern matching")
                                }
                            } else if let Pat::Ident(pat) = stmt.pat {
                                Doc::text(format!("\"{}\"", pat.ident))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(parenthesize(
                                        stmt.let_token.span.to_doc(st.clone())
                                            .append(Doc::text(","))
                                            .append(Doc::space())
                                            .append(Doc::text("Infer"))
                                    ))
                            } else {
                                panic!("bindings must use identifiers, not pattern matching")
                            }).append(Doc::text(","))
                                .append(Doc::space())
                                .append(match stmt.init {
                                    Some((_, expr)) =>
                                        Doc::text("(*=*)")
                                        .append(Doc::space())
                                        .append(parenthesize(expr.to_doc(st.clone()).nest(2))),
                                    None => panic!("we don't support uninitialized bindings"),
                                })
                                .append(Doc::text(","))
                                .append(Doc::space())
                                .append(acc)
                        ))
                ),
                Stmt::Expr(expr) => {
                    if acc == Doc::nil() {
                        parenthesize(expr.to_doc(st.clone()).nest(2))
                    } else {
                        parenthesize(expr.to_doc(st.clone()).nest(2))
                            .append(Doc::space())
                            .append(Doc::text(">>"))
                            .append(Doc::space())
                            .append(acc)
                    }
                },
                Stmt::Semi(expr, _) => parenthesize(
                    expr.to_doc(st.clone())
                        .append(Doc::space())
                        .append(Doc::text(">>"))
                        .append(Doc::space())
                        .append(acc)
                ),
                Stmt::Item(_) => panic!("no items in blocks"),
            }
        })
    }
}

impl PrettyPrint for Pat {
    fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Pat::Ident(pat) = self {
            return Doc::text(format!("\"{}\"", pat.ident))
        }

        if let Pat::Type(pat) = self {
            return pat.pat.to_doc(st.clone())
                .append(Doc::space())
                .append(Doc::text("@:"))
                .append(Doc::space())
                .append(parenthesize(pat.ty.to_doc(st.clone())))
                .group()
        }

        if let Pat::Wild(_) = self {
            return Doc::text("\"\"")
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for Type {
    fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Type::Infer(ty) = self {
            return parenthesize(
                ty.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(Doc::text("Infer"))
            )
        }

        if let Type::Reference(ty) = self {
            let lft = match ty.lifetime.as_ref() {
                Some(lft) => lft,
                None => panic!("you need to include lifetime annotations in types!"),
            };
            return parenthesize(
                ty.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Ref")
                            .append(Doc::space())
                            .append(parenthesize(
                                parenthesize(
                                    lft.span().to_doc(st.clone())
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        .append(quote(Doc::text(format!("{}", lft.ident)))))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(ty.mutability.to_doc(st.clone()))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(parenthesize(ty.elem.to_doc(st.clone())))
                            ))
                    )
            )
        }

        if let Type::Array(ty) = self {
            return parenthesize(
                ty.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Array")
                            .append(Doc::space())
                            .append(parenthesize(
                                ty.elem.to_doc(st.clone())
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(if let Expr::Lit(len) = ty.len {
                                        if let Lit::Int(n) = len.lit {
                                            let value = n.base10_parse::<usize>().expect(
                                                "array length must be a valid usize"
                                            );
                                            Doc::text(format!("{}", value))
                                        } else {
                                            panic!("array lengths must be integers")
                                        }
                                    } else {
                                        panic!("we only support array types with literal length")
                                    })
                            ))
                    )
            )
        }

        if let Type::Tuple(ty) = self {
            return parenthesize(
                ty.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(if ty.elems.is_empty() {
                        Doc::text("BaseTy")
                            .append(Doc::space())
                            .append(Doc::text("Unit"))
                            .group()
                    } else {
                        Doc::text("tupty")
                            .append(Doc::space())
                            .append(
                                Doc::text("[")
                                    .append(
                                        Doc::intersperse(
                                            ty.elems.into_iter().map(|ty| ty.to_doc(st.clone())),
                                            Doc::text(";").append(Doc::space())
                                        )
                                    )
                                    .append(Doc::text("]"))
                                    .group()
                            )
                            .group()
                    })
            )
        }

        if let Type::BareFn(ty) = self {
            let ty_span = ty.span();
            return parenthesize(
                ty_span.to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(Doc::text("Fun"))
                    .append(Doc::space())
                    .append(parenthesize(
                        Doc::nil()
                            // environment variables
                            .append(Doc::text("[]"))
                            .append(Doc::text(","))
                            .append(Doc::space())
                            // lifetime variables
                            .append(match ty.lifetimes {
                                Some(bound) =>
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            bound.lifetimes.into_iter().map(|lft| {
                                                lft.to_doc(st.clone())
                                            }),
                                            Doc::text(";").append(Doc::space())
                                        ))
                                        .append(Doc::text("]")),
                                None => Doc::text("[]"),
                            })
                            .append(Doc::text(","))
                            .append(Doc::space())
                            // type variables
                            .append(Doc::text("[]"))
                            .append(Doc::text(","))
                            .append(Doc::space())
                            // parameter types
                            .append(
                                Doc::text("[")
                                    .append(Doc::intersperse(
                                        ty.inputs.into_iter().map(|arg| arg.ty.to_doc(st.clone())),
                                        Doc::text(";").append(Doc::space())
                                    ))
                                    .append(Doc::text("]"))
                                    .group()
                            )
                            .append(Doc::text(","))
                            .append(Doc::space())
                            // captured environment
                            .append(Doc::text("Unboxed"))
                            .append(Doc::text(","))
                            .append(Doc::space())
                            // return type
                            .append(parenthesize(match ty.output {
                                ReturnType::Default =>
                                    ty_span.to_doc(st.clone())
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(Doc::text("BaseTy")
                                            .append(Doc::space())
                                            .append(Doc::text("Unit"))
                                    )
                                    .group(),
                                ReturnType::Type(_, ty) => ty.to_doc(st.clone()),
                            }))
                    ))
            )
        }

        if let Type::Path(ty) = self {
            let ty_name = ty.path.segments.iter().fold(
                String::new(),
                |mut acc, seg| {
                    acc.push_str("::");
                    acc.push_str(&format!("{}", seg.ident));
                    acc
                }
            ).split_off(2);

            return parenthesize(
                ty.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(if NUMS.contains(&&ty_name[..]) {
                        Doc::text("BaseTy")
                            .append(Doc::space())
                            .append(Doc::text("U32"))
                            .group()
                    } else if ty_name == "bool" {
                        Doc::text("BaseTy")
                            .append(Doc::space())
                            .append(Doc::text("Bool"))
                            .group()
                    } else {
                        resolve_name(st.clone(), ty.path, true).0
                    })
            )
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrintPlaceExpr for ExprPath {
    fn to_place_expr_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        return parenthesize(
            self.span().to_doc(st.clone())
                .append(Doc::text(","))
                .append(Doc::space())
                .append(parenthesize(
                    quote(self.path.to_doc(st.clone()))
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(Doc::text("[]"))
                    .group(),
                )),
        );
    }
}

impl PrettyPrintPlaceExpr for ExprField {
    fn to_place_expr_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        return parenthesize(
            parenthesize(self.base.to_place_expr_doc(st.clone()))
                .append(Doc::space())
                .append(match self.member {
                Member::Named(field) => Doc::text("$.$")
                    .append(Doc::space())
                    .append(Doc::text(format!("\"{}\"", field))),
                Member::Unnamed(idx) => Doc::text("$.")
                    .append(Doc::space())
                    .append(Doc::text(format!("{}", idx.index))),
                })
        );
    }
}

impl PrettyPrintPlaceExpr for Expr {
    fn to_place_expr_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Expr::Paren(expr) = self {
            return parenthesize(expr.expr.to_place_expr_doc(st.clone()))
        }

        if let Expr::Path(expr) = self {
            return expr.to_place_expr_doc(st.clone())
        }

        if let Expr::Unary(expr) = self {
            return parenthesize(
                expr.op.to_doc(st.clone())
                    .append(Doc::space())
                    .append(parenthesize(expr.expr.to_place_expr_doc(st.clone())))
            )
        }

        if let Expr::Field(expr) = self {
            return parenthesize(
                parenthesize(expr.base.to_place_expr_doc(st.clone()))
                    .append(Doc::space())
                    .append(match expr.member {
                        Member::Named(field) =>
                            Doc::text("$.$")
                            .append(Doc::space())
                            .append(Doc::text(format!("\"{}\"", field))),
                        Member::Unnamed(idx) =>
                            Doc::text("$.")
                            .append(Doc::space())
                            .append(Doc::text(format!("{}", idx.index))),
                    })
            )
        }

        self.to_doc(st.clone())
    }
}

impl PrettyPrint for Expr {
  fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Expr::Block(expr) = self {
            return parenthesize(expr.block.to_doc(st.clone()))
        }

        if let Expr::Group(expr) = self {
            return parenthesize(expr.expr.to_doc(st.clone()))
        }

        if let Expr::Lit(expr) = self {
            return expr.lit.to_doc(st.clone())
        }

        if let Expr::Paren(expr) = self {
            return parenthesize(expr.expr.to_doc(st.clone()))
        }

        if let Expr::Reference(expr) = self {
            let mut lft = gensym();
            for attr in expr.attrs.iter() {
                if let Ok(Meta::NameValue(attr)) = attr.parse_meta() {
                    if attr.path.is_ident("lft") {
                        if let Lit::Str(lit) = attr.lit {
                            lft = Doc::text(lit.value());
                        } else {
                            panic!("lifetime annotation on borrows must use string literals")
                        }
                    }
                }
            }

            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Borrow")
                            .append(Doc::space())
                            .append(parenthesize(
                                parenthesize(expr.span().to_doc(st.clone())
                                             .append(Doc::text(","))
                                             .append(Doc::space())
                                             .append(lft))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.mutability.to_doc(st.clone()))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.expr.to_place_expr_doc(st.clone()))
                            ))
                            .group()
                    )
            )
        }

        if let Expr::Unary(expr) = self {
            let mut cmd = "Move";
            for attr in expr.attrs.iter() {
                if attr.path.is_ident("drop") {
                    cmd = "Drop"
                }
            }

            return parenthesize(expr.span().to_doc(st.clone())
                .append(Doc::text(","))
                .append(Doc::space())
                .append(
                    Doc::text(cmd)
                        .append(Doc::space())
                        .append(parenthesize(
                            expr.op.to_doc(st.clone())
                                .append(Doc::space())
                                .append(parenthesize(expr.expr.to_place_expr_doc(st.clone())))
                        ))
                )
            )
        }

        if let Expr::Binary(expr) = self {
            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("BinOp")
                            .append(Doc::space())
                            .append(parenthesize(
                                expr.op.to_doc(st.clone())
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(parenthesize(expr.left.to_doc(st.clone())))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(parenthesize(expr.right.to_doc(st.clone())))
                            ))
                            .group()
                    )
            )
        }

      if let Expr::Path(expr) = self {
            let mut cmd = "Move";
            for attr in expr.attrs.iter() {
                if attr.path.is_ident("drop") {
                    cmd = "Drop"
                }
            }

            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text(cmd)
                            .append(Doc::space())
                            .append(parenthesize(expr.to_place_expr_doc(st.clone())))
                    )
            )
        }

        if let Expr::Field(expr) = self {
            let mut cmd = "Move";
            for attr in expr.attrs.iter() {
                if attr.path.is_ident("drop") {
                cmd = "Drop"
                }
            }

            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text(cmd)
                        .append(Doc::space())
                        .append(parenthesize(expr.to_place_expr_doc(st.clone()))),
                    )
            );
        }

        if let Expr::Index(expr) = self {
            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(Doc::text("Idx")
                            .append(Doc::space())
                            .append(parenthesize(
                                expr.expr.to_place_expr_doc(st.clone())
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.index.to_doc(st.clone()))
                            ))
                            .group()
                    )
            )
        }

        if let Expr::Tuple(expr) = self {
            if expr.elems.is_empty() {
                return parenthesize(
                    expr.span().to_doc(st.clone())
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(
                            Doc::text("Prim")
                                .append(Doc::space())
                                .append(Doc::text("Unit"))
                                .group()
                        )
                )
            } else {
                return parenthesize(
                    expr.span().to_doc(st.clone())
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(Doc::text("Tup")
                                .append(Doc::space())
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            expr.elems.into_iter().map(|expr| expr.to_doc(st.clone())),
                                            Doc::text(";").append(Doc::space())
                                        ))
                                        .append(Doc::text("]"))
                                        .group()
                                )
                        )
                )
            }
        }

        if let Expr::If(expr) = self {
            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Branch")
                            .append(Doc::space())
                            .append(parenthesize(
                                expr.cond.to_doc(st.clone())
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.then_branch.to_doc(st.clone()))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(match expr.else_branch {
                                        Some((_, els)) => els.to_doc(st.clone()),
                                        None => parenthesize(
                                            expr.if_token.span().to_doc(st.clone())
                                                .append(Doc::text(","))
                                                .append(Doc::space())
                                                .append(
                                                    Doc::text("Prim")
                                                        .append(Doc::space())
                                                        .append(Doc::text("Unit"))
                                                        .group()
                                                )
                                       ),
                                    })
                            ))
                            .group()
                    )
            )
        }

        if let Expr::Array(expr) = self {
            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Array")
                            .append(Doc::space())
                            .append(Doc::text("[")
                                    .append({
                                        Doc::intersperse(
                                            expr.elems.into_iter().map(|expr| expr.to_doc(st.clone())),
                                            Doc::text(";").append(Doc::space())
                                        )
                                    })
                                    .append(Doc::text("]"))
                                    .group()
                            )
                    )
            )
        }

        if let Expr::Repeat(expr) = self {
            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Array")
                            .append(Doc::space())
                            .append(Doc::text("[")
                                    .append({
                                        if let Expr::Lit(ExprLit { lit: Lit::Int(int), .. }) =
                                            *expr.len {
                                            let rng = int.base10_digits()
                                                    .parse()
                                                    .expect("encountered non-number literal int");
                                            let doc = parenthesize(expr.expr.to_doc(st.clone()));
                                            Doc::intersperse(
                                                (0..rng).map(|_| {
                                                    doc.clone()
                                                }),
                                                Doc::text(";").append(Doc::space())
                                            )
                                        } else {
                                            panic!("we don't support non-literal length repeats")
                                        }
                                    })
                                    .append(Doc::text("]"))
                                    .group()
                            )
                    )
            )
        }

        if let Expr::Assign(expr) = self {
            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Assign")
                            .append(Doc::space())
                            .append(parenthesize(
                                parenthesize(expr.left.to_place_expr_doc(st.clone()))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(parenthesize(expr.right.to_doc(st.clone())))
                            ))
                            .group()
                    )
            )
        }

        if let Expr::AssignOp(expr) = self {
            // We implement assign ops by desugaring them into assignment and the standard binop
            return Expr::Assign(ExprAssign {
                attrs: expr.attrs.clone(),
                left: expr.left.clone(),
                eq_token: syn::token::Eq { spans: [match expr.op {
                    BinOp::AddEq(op) => op.spans[1],
                    BinOp::SubEq(op) => op.spans[1],
                    BinOp::MulEq(op) => op.spans[1],
                    BinOp::DivEq(op) => op.spans[1],
                    BinOp::RemEq(op) => op.spans[1],
                    BinOp::BitXorEq(op) => op.spans[1],
                    BinOp::BitAndEq(op) => op.spans[1],
                    BinOp::BitOrEq(op) => op.spans[1],
                    BinOp::ShlEq(op) => op.spans[2],
                    BinOp::ShrEq(op) => op.spans[2],
                    _ => unreachable!()
                }] },
                right: Box::new(Expr::Binary(ExprBinary {
                    attrs: expr.attrs,
                    left: expr.left,
                    op: match expr.op {
                        BinOp::AddEq(op) => BinOp::Add(syn::token::Add { spans: [op.spans[0]] }),
                        BinOp::SubEq(op) => BinOp::Sub(syn::token::Sub { spans: [op.spans[0]] }),
                        BinOp::MulEq(op) => BinOp::Mul(syn::token::Star { spans: [op.spans[0]] }),
                        BinOp::DivEq(op) => BinOp::Div(syn::token::Div { spans: [op.spans[0]] }),
                        BinOp::RemEq(op) => BinOp::Rem(syn::token::Rem { spans: [op.spans[0]] }),
                        BinOp::BitXorEq(op) => BinOp::BitXor(syn::token::Caret {
                            spans: [op.spans[0]]
                        }),
                        BinOp::BitAndEq(op) => BinOp::BitAnd(syn::token::And {
                            spans: [op.spans[0]]
                        }),
                        BinOp::BitOrEq(op) => BinOp::BitOr(syn::token::Or {
                            spans: [op.spans[0]]
                        }),
                        BinOp::ShlEq(op) => BinOp::Shl(syn::token::Shl {
                            spans: [op.spans[0], op.spans[1]]
                        }),
                        BinOp::ShrEq(op) => BinOp::Shr(syn::token::Shr {
                            spans: [op.spans[0], op.spans[1]]
                        }),
                        _ => unreachable!()
                    },
                    right: expr.right,
                }))
            }).to_doc(st.clone())
        }

        if let Expr::Loop(expr) = self {
                return parenthesize(
                    expr.span().to_doc(st.clone())
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(
                            Doc::text("While")
                                .append(Doc::space())
                                .append(parenthesize(
                                    parenthesize(
                                        expr.loop_token.span().to_doc(st.clone())
                                            .append(Doc::text(","))
                                            .append(Doc::space())
                                            .append(Doc::text("Prim"))
                                            .append(Doc::space())
                                            .append(Doc::text("True"))
                                    ).group()
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        .group()
                                        .nest(2)
                                        .append(parenthesize(expr.body.to_doc(st.clone())))
                                ))
                                .group()
                        )
                )
        }

        if let Expr::While(expr) = self {
            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("While")
                            .append(Doc::space())
                            .append(parenthesize(
                                expr.cond.to_doc(st.clone())
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .group()
                                    .nest(2)
                                    .append(parenthesize(expr.body.to_doc(st.clone())))
                            ))
                            .group()
                    )
            )
        }

        if let Expr::ForLoop(expr) = self {
            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("For")
                            .append(Doc::space())
                            .append(parenthesize(
                                    expr.pat.to_doc(st.clone())
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        .append(parenthesize(expr.expr.to_doc(st.clone())))
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        .group()
                                        .nest(2)
                                        .append(parenthesize(expr.body.to_doc(st.clone())))
                            ))
                            .group()
                    )
            )
        }

        if let Expr::Range(expr) = self {
            let span = expr.span().clone();
            // we only support _finite_ ranges (by elaboration into an array)
            if let Some(Expr::Lit(ExprLit { lit: Lit::Int(n1), .. })) = expr.from.map(|x| *x) {
                if let Some(Expr::Lit(ExprLit { lit: Lit::Int(n2), .. })) = expr.to.map(|x| *x) {
                    let num1: usize = n1.base10_digits()
                            .parse()
                            .expect("encountered non-number literal int");
                    let num2: usize = n2.base10_digits()
                            .parse()
                            .expect("encountered non-number literal int");
                    return parenthesize(span.to_doc(st.clone())
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(Doc::text("Array"))
                        .append(Doc::space())
                        .append(parenthesize(
                            Doc::text("[")
                                .append(match expr.limits {
                                    RangeLimits::HalfOpen(range) =>
                                        Doc::intersperse(
                                            (num1..num2).map(|n| {
                                                parenthesize(
                                                    range.span().to_doc(st.clone())
                                                        .append(Doc::text(","))
                                                        .append(Doc::space())
                                                        .append(Doc::text("Prim"))
                                                        .append(Doc::space())
                                                        .append(parenthesize(
                                                            Doc::text("Num")
                                                                .append(Doc::space())
                                                                .append(Doc::text(format!("{}", n)))
                                                        ))
                                                )
                                            }),
                                            Doc::text(";").append(Doc::space())
                                        ),
                                    RangeLimits::Closed(range) =>
                                        Doc::intersperse(
                                            (num1..=num2).map(|n| {
                                                parenthesize(
                                                    range.span().to_doc(st.clone())
                                                        .append(Doc::text(","))
                                                        .append(Doc::space())
                                                        .append(Doc::text("Prim"))
                                                        .append(Doc::space())
                                                        .append(parenthesize(
                                                            Doc::text("Num")
                                                                .append(Doc::space())
                                                                .append(Doc::text(format!("{}", n)))
                                                        ))
                                                )
                                            }),
                                            Doc::text(";").append(Doc::space())
                                        ),
                                })
                                .append(Doc::text("]"))
                        )))
                } else {
                    panic!("we don't support non-literal or non-finite ranges")
                }
            } else {
                panic!("we don't support non-literal or non-finite ranges")
            }
        }

        if let Expr::Closure(expr) = self {
            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Fun")
                            .append(Doc::space())
                            .append(parenthesize(
                                Doc::text("[]")
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(Doc::text("[]"))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(
                                        Doc::text("[")
                                            .append(Doc::intersperse(
                                                expr.inputs.into_iter().map(|arg| arg.to_doc(st.clone())),
                                                Doc::text(";").append(Doc::space())
                                            ))
                                            .append(Doc::text("]"))
                                    )
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(match expr.output {
                                        ReturnType::Default => Doc::text("None"),
                                        ReturnType::Type(_, ty) => Doc::text("Some")
                                            .append(Doc::space())
                                            .append(parenthesize(ty.to_doc(st.clone())
                                            ))
                                            .group()
                                    })
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.body.to_doc(st.clone()))
                            ))
                    )
            )
        }

        if let Expr::Macro(expr) = self {
            let macro_name = expr.mac.path.segments.iter().fold(
                String::new(),
                |mut acc, seg| {
                    acc.push_str("::");
                    acc.push_str(&format!("{}", seg.ident));
                    acc
                }
            ).split_off(2);
            if MACROS.contains(&&macro_name[..]) {
                return parenthesize(
                    expr.span().to_doc(st.clone())
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(
                            Doc::text("Abort")
                                .append(Doc::space())
                                .append(if macro_name == "unimplemented" {
                                    quote(Doc::text("abort: unimplemented"))
                                } else if macro_name == "unreachable" {
                                    quote(Doc::text("abort: unreachable"))
                                } else if expr.mac.tokens.is_empty () {
                                    quote(Doc::text("abort: no message provided"))
                                } else {
                                    match syn::parse2::<Lit>(expr.mac.tokens) {
                                        Ok(lit) => lit.to_doc(st.clone()),
                                        Err(_) => panic!("we don't support panic or \
                                                          aborts with non-literal arguments")
                                    }
                                })
                                .group()
                        )
                );
            } else {
                panic!("we don't support the macro: {}!", macro_name);
            }
        }

        if let Expr::Struct(expr) = self {
            let last_args1 = expr.path.segments.last().unwrap().arguments.clone();
            let last_args2 = last_args1.clone();
            return parenthesize(
                expr.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("RecStruct")
                            .append(Doc::space())
                            .append(parenthesize(
                                quote(expr.path.to_doc(st.clone()))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    // provenance variable arguments
                                    .append(
                                        Doc::text("[")
                                            .append(last_args1.to_lifetime_generics_doc(st.clone()))
                                            .append(Doc::text("]"))
                                            .group()
                                    )
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    // type variable arguments
                                    .append(
                                        Doc::text("[")
                                            .append(last_args2.to_type_generics_doc(st.clone()))
                                            .append(Doc::text("]"))
                                            .group()
                                    )
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    // arguments
                                    .append(
                                        Doc::text("[")
                                            .append(Doc::intersperse(
                                                expr.fields
                                                    .into_iter()
                                                    .map(|field| {
                                                        parenthesize(field.to_doc(st.clone()))
                                                    }),
                                                Doc::text(";").append(Doc::space())
                                            ))
                                            .append(Doc::text("]"))
                                            .group()
                                    )
                            ))
                            .group()
                    )
            )
        }

        if let Expr::Call(expr) = self {
            if let Expr::Path(func) = &*expr.func {
                let last_args1 = func.path.segments.last().unwrap().arguments.clone();
                let last_args2 = last_args1.clone();
                let (resolved, typ) = resolve_name(st.clone(), func.path.clone(), false);

                if let ResolutionType::FunName = typ {
                    return parenthesize(
                        expr.span().to_doc(st.clone())
                            .append(Doc::text(","))
                            .append(Doc::space())
                            .append(
                                Doc::text("App")
                                    .append(Doc::space())
                                    .append(parenthesize(
                                        parenthesize(
                                            func.path.span().to_doc(st.clone())
                                                .append(Doc::text(","))
                                                .append(Doc::space())
                                                .append(resolved)
                                        )
                                            .append(Doc::text(","))
                                            .append(Doc::space())
                                            // environment arguments
                                            .append(
                                                Doc::text("[")
                                                    .append(expr.attrs.to_env_doc(st.clone()))
                                                    .append(Doc::text("]"))
                                                    .group()
                                            )
                                            .append(Doc::text(","))
                                            .append(Doc::space())
                                            // provenance variable arguments
                                            .append(
                                                Doc::text("[")
                                                    .append(last_args1
                                                            .to_lifetime_generics_doc(st.clone()))
                                                    .append(Doc::text("]"))
                                                    .group()
                                            )
                                            .append(Doc::text(","))
                                            .append(Doc::space())
                                            // type variable arguments
                                            .append(
                                                Doc::text("[")
                                                    .append(last_args2
                                                            .to_type_generics_doc(st.clone()))
                                                    .append(Doc::text("]"))
                                                    .group()
                                            )
                                            .append(Doc::text(","))
                                            .append(Doc::space())
                                            // arguments
                                            .append(
                                                Doc::text("[")
                                                    .append(Doc::intersperse(
                                                        expr.args
                                                            .into_iter()
                                                            .map(|expr| {
                                                                parenthesize(expr.to_doc(st.clone()))
                                                            }),
                                                        Doc::text(";").append(Doc::space())
                                                    ))
                                                    .append(Doc::text("]"))
                                                    .group()
                                            )
                                    ))
                                    .group()
                            )
                    )
                }

                if let ResolutionType::StructName = typ {
                    return parenthesize(
                        expr.span().to_doc(st.clone())
                            .append(Doc::text(","))
                            .append(Doc::space())
                            .append(
                                resolved
                                    .append(Doc::space())
                                    // arguments
                                    .append(
                                        Doc::text("[")
                                            .append(Doc::intersperse(
                                                expr.args
                                                    .into_iter()
                                                    .map(|expr| {
                                                        parenthesize(expr.to_doc(st.clone()))
                                                    }),
                                                Doc::text(";").append(Doc::space())
                                            ))
                                            .append(Doc::text("]"))
                                            .group()
                                    )
                                    .group()
                            )
                            .group()
                    )
                }

                unreachable!()
            } else if let Expr::Closure(_) = *expr.func {
                return parenthesize(
                    expr.span().to_doc(st.clone())
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(
                            Doc::text("App")
                                .append(Doc::space())
                                .append(parenthesize(
                                    parenthesize(expr.func.to_doc(st.clone()))
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        // provenance variable arguments
                                        .append(
                                            Doc::text("[")
                                                .append(Doc::text("]"))
                                                .group()
                                        )
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        // type variable arguments
                                        .append(
                                            Doc::text("[")
                                                .append(Doc::text("]"))
                                                .group()
                                        )
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        // arguments
                                        .append(
                                            Doc::text("[")
                                                .append(Doc::intersperse(
                                                    expr.args
                                                        .into_iter()
                                                        .map(|expr| {
                                                            parenthesize(expr.to_doc(st.clone()))
                                                        }),
                                                    Doc::text(";").append(Doc::space())
                                                ))
                                                .append(Doc::text("]"))
                                                .group()
                                        )
                                ))
                                .group()
                        )
                )
            } else if let Expr::Paren(expr) = *expr.func {
                return parenthesize(expr.expr.to_doc(st.clone()))
            } else if let Expr::Call(_) = *expr.func {
                panic!("unimplemented: application in function call position")
            } else {
                eprintln!("{:#?}", expr.func);
                panic!("can't apply something other than an identifier or a closure")
            }
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for Lifetime {
  fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
    parenthesize(
     self.span().to_doc(st.clone())
        .append(Doc::text(","))
        .append(Doc::space())
        .append(quote(Doc::text(format!("{}", self.ident)))),
    )
  }
}

impl PrettyPrint for LifetimeDef {
  fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
      self.lifetime.to_doc(st.clone())
  }
}

impl PrettyPrint for WherePredicate {
  fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            WherePredicate::Type(_) => {
                panic!("Oxide does not support traits or trait bounds.")
            },
            WherePredicate::Eq(_) => {
                panic!("Rust and Oxide do not support equality predicates in where clauses.")
            },
            // lifetime bounds
            WherePredicate::Lifetime(mut pred) => {
                if pred.bounds.len() != 1 {
                    panic!("reducer requires one provenance per bound!");
                }

                // we swap directions because "b outlives a" means "a flows into b"
                let lft = pred.bounds.pop().unwrap().into_value();
                parenthesize(
                    lft.to_doc(st.clone())
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(pred.lifetime.to_doc(st.clone()))
                )
            }
        }
    }
}

impl PrettyPrint for Path {
    fn to_doc(self, _: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::intersperse(
            self.segments.into_iter().map(|seg| Doc::text(format!("{}", seg.ident))),
            Doc::text("::")
        )
    }
}

impl PrettyPrint for FieldValue {
    fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        parenthesize(
            (match self.member {
               Member::Named(id) => quote(Doc::text(format!("{}", id))),
               Member::Unnamed(idx) => quote(Doc::text(format!("{}", idx.index))),
            }).append(Doc::text(","))
                .append(Doc::space())
                .append(self.expr.to_doc(st.clone()))
        )
    }
}

impl PrettyPrint for UnOp {
    fn to_doc(self, _: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::text(match self {
            UnOp::Deref(_) => "~*",
            UnOp::Not(_) => "Not",
            UnOp::Neg(_) => "Neg",
        })
    }
}

impl PrettyPrint for BinOp {
    fn to_doc(self, _: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::text(match self {
            BinOp::Add(_) => "Add",
            BinOp::Sub(_) => "Sub",
            BinOp::Mul(_) => "Mul",
            BinOp::Div(_) => "Div",
            BinOp::Rem(_) => "Rem",
            BinOp::And(_) => "And",
            BinOp::Or(_) => "Or",
            BinOp::BitXor(_) => "BitXor",
            BinOp::BitAnd(_) => "BitAnd",
            BinOp::BitOr(_) => "BitOr",
            BinOp::Shl(_) => "Shl",
            BinOp::Shr(_) => "Shr",
            BinOp::Eq(_) => "Eq",
            BinOp::Lt(_) => "Lt",
            BinOp::Le(_) => "Le",
            BinOp::Ne(_) => "Ne",
            BinOp::Ge(_) => "Ge",
            BinOp::Gt(_) => "Gt",
            _ => unreachable!() /* should be handled by desugaring */
        })
    }
}

impl PrettyPrint for Option<syn::token::Mut> {
    fn to_doc(self, _: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            Some(_) => Doc::text("Unique"),
            None => Doc::text("Shared"),
        }
    }
}

impl PrettyPrint for Lit {
  fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Lit::Bool(bool) = self {
            return parenthesize(
                bool.span.to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        if bool.value {
                            Doc::text("Prim")
                                .append(Doc::space())
                                .append(Doc::text("True"))
                        } else {
                            Doc::text("Prim")
                                .append(Doc::space())
                                .append(Doc::text("False"))
                        }
                    )
            )
        }

        if let Lit::Int(int) = self {
            return parenthesize(
                int.span().to_doc(st.clone())
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Prim")
                            .append(Doc::space())
                            .append(parenthesize(
                                Doc::text("Num")
                                    .append(Doc::space())
                                    .append(Doc::text(format!("{}", int.base10_digits())))
                            ))
                    )
            )
        }

        if let Lit::Str(str) = self {
            return quote(Doc::text(str.value()))
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for FnArg {
    fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            FnArg::Typed(cap) =>
                cap.pat.to_doc(st.clone())
                .append(Doc::space())
                .append(Doc::text("@:"))
                .append(Doc::space())
                .append(parenthesize(cap.ty.to_doc(st.clone())))
                .group(),
            _ => Doc::nil(),
        }
    }
}

impl PrettyPrint for LineColumn {
    fn to_doc(self, _: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        parenthesize(
            Doc::text(format!("{}", self.line))
                .append(Doc::text(","))
                .append(Doc::space())
                .append(Doc::text(format!("{}", self.column)))
        )
    }
}

// Not sure why, but source files are semver exempt in proc-macro2 API, so, here's a hack
impl PrettyPrint for Span {
    #[cfg(procmacro2_semver_exempt)]
    fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        parenthesize(
            quote(Doc::text(match self.source_file().path().file_name() {
                Some(name) => name.to_string_lossy().into_owned(),
                None => "unknown_file".to_owned(),
            }))
                .append(Doc::text(","))
                .append(Doc::space())
                .append(self.start().to_doc(st.clone()))
                .append(Doc::text(","))
                .append(Doc::space())
                .append(self.end().to_doc(st.clone()))
        )
    }

    #[cfg(not(procmacro2_semver_exempt))]
    fn to_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        parenthesize(
            quote(Doc::text("unknown_file"))
                .append(Doc::text(","))
                .append(Doc::space())
                .append(self.start().to_doc(st.clone()))
                .append(Doc::text(","))
                .append(Doc::space())
                .append(self.end().to_doc(st.clone()))
        )
    }
}

trait PrettyPrintLifetimeGenerics {
    fn to_lifetime_generics_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>>;
}

impl PrettyPrintLifetimeGenerics for PathArguments {
    fn to_lifetime_generics_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            PathArguments::None => Doc::nil(),
            PathArguments::Parenthesized(_) => Doc::text("(failwith \"unimplemented\")"),
            PathArguments::AngleBracketed(bracketed) => Doc::intersperse(
                bracketed.args.into_iter().filter(|arg| {
                    if let GenericArgument::Lifetime(_) = arg { true } else { false }
                }).map(|arg| match arg {
                    GenericArgument::Lifetime(lft) => lft.to_doc(st.clone()),
                    _ => unreachable!()
                }),
                Doc::text(";").append(Doc::space())
            )
        }
    }
}

trait PrettyPrintTypeGenerics {
    fn to_type_generics_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>>;
}

impl PrettyPrintTypeGenerics for PathArguments {
    fn to_type_generics_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            PathArguments::None => Doc::nil(),
            PathArguments::Parenthesized(_) => Doc::text("(failwith \"unimplemented\")"),
            PathArguments::AngleBracketed(bracketed) => Doc::intersperse(
                bracketed.args.into_iter().filter(|arg| {
                    if let GenericArgument::Type(_) = arg { true } else { false }
                }).map(|arg| match arg {
                    GenericArgument::Type(typ) => typ.to_doc(st.clone()),
                    _ => unreachable!()
                }),
                Doc::text(";").append(Doc::space())
            )
        }
    }
}

trait PrettyPrintEnvironments {
    fn to_env_doc(self, st: CompilerState) -> Doc<'static, BoxDoc<'static, ()>>;
}

impl PrettyPrintEnvironments for Vec<Attribute> {
  fn to_env_doc(self, _: CompilerState) -> Doc<'static, BoxDoc<'static, ()>> {
    let envs = self
      .iter()
      .filter(|attr| attr.path.segments.len() == 1)
      .filter(|attr| {
        let attr_id = attr.path.segments.clone().pop().unwrap().into_value();
        attr_id.ident == "envs"
      })
      .flat_map(|attr| {
        match attr
          .parse_meta()
          .expect("malformed input to envs annotations")
        {
          Meta::List(lst) => lst.nested,
          _ => panic!("envs attribute should be a structured list"),
        }
      });

      Doc::intersperse(
          envs.map(|meta| match meta {
              NestedMeta::Meta(Meta::Path(path)) => Doc::text("EnvOf")
                  .append(Doc::space())
                  .append(Doc::text(format!("\"{}\"",
                      path.get_ident().expect("envs annotations should only use identifiers")
                  ))),
              NestedMeta::Meta(_) => panic!("malformed envs annotation input"),
              NestedMeta::Lit(_) => panic!("envs annotations should not contain literals"),
          }),
          Doc::text(";").append(Doc::space())
      )
  }
}
