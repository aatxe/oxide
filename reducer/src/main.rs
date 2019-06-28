use std::env;
use std::fs::File;
use std::io::Read;
use std::process;

use pretty::{BoxDoc, Doc};
use proc_macro2::{LineColumn, Span};
use syn::{Block, Expr, Fields, FnArg, Item, Lit, Member, Pat, Path, ReturnType, Stmt, Type, UnOp};
use syn::{BinOp, ExprAssign, ExprBinary, ExprLit, GenericArgument, PathArguments, RangeLimits};
use syn::spanned::Spanned;

type PP = Doc<'static, BoxDoc<'static, ()>>;

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
            eprintln!("Usage: dump-syntax path/to/filename.rs");
            process::exit(1);
        }
    };

    let mut file = File::open(&filename).expect("Unable to open file");

    let mut src = String::new();
    file.read_to_string(&mut src).expect("Unable to read file");

    let syntax = syn::parse_file(&src).expect("Unable to parse file");

    let docs = syntax.items.into_iter().map(|item| parenthesize(item.to_doc()));

    let global_env = Doc::text("[")
        .append(Doc::intersperse(docs, Doc::text(";").append(Doc::space())).nest(2))
        .append(Doc::text("]"))
        .group();

    let program =
        Doc::text("let")
        .append(Doc::space())
        .append(Doc::text("prog"))
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
        .append(Doc::text("prog"))
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
                .append(Doc::text("prog"))
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
                                .append(Doc::text("prog"))
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
fn resolve_name(path: Path, is_type: bool) -> PP {
    let last_args1 = path.segments.last().unwrap().value().arguments.clone();
    let last_args2 = last_args1.clone();
    let name = path.segments.iter().fold(String::new(), |mut acc, seg| {
        acc.push_str(&format!("{}", seg.ident));
        acc
    });

    if name == name.to_lowercase() {
        Doc::text("Fn")
            .append(Doc::space())
            .append(quote(Doc::text(name)))
            .group()
    } else if is_type && name.len() == 1 {
        Doc::text("TyVar")
            .append(Doc::space())
            .append(quote(Doc::text(name)))
            .group()
    } else {
        Doc::text("Struct")
            .append(Doc::space())
            .append(parenthesize(
                quote(Doc::text(name))
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("[")
                            .append(last_args1.to_lifetime_generics_doc())
                            .append(Doc::text("]"))
                            .group()
                    )
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("[")
                            .append(last_args2.to_type_generics_doc())
                            .append(Doc::text("]"))
                            .group()
                    )
            ))
            .group()
    }
}

trait PrettyPrint {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>>;
}

trait PrettyPrintPlaceExpr {
    fn to_place_expr_doc(self) -> Doc<'static, BoxDoc<'static, ()>>;
}

impl PrettyPrint for Item {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Item::Fn(item) = self {
            return Doc::text("fn")
                .append(Doc::space())
                .append(Doc::text(format!("\"{}\"", item.ident)))
                .group()
                // provenance variables
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(
                            Doc::intersperse(
                                item.decl.generics.lifetimes().map(|lft| {
                                    Doc::text(format!("\"{}\"", lft.lifetime.ident))
                                }),
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
                                item.decl.generics.type_params().map(|tyvar| {
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
                                item.decl.inputs.into_iter().map(|arg| arg.to_doc()),
                                Doc::text(";").append(Doc::space())
                            )
                        )
                        .append(Doc::text("]"))
                        .group()
                )
                // return type
                .append(Doc::space())
                .append(parenthesize(match item.decl.output {
                    ReturnType::Default => item.decl.output.span().to_doc()
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(Doc::text("BaseTy")
                                .append(Doc::space())
                                .append(Doc::text("Unit"))
                        )
                        .group(),
                    ReturnType::Type(_, ty) => ty.to_doc(),
                }))
                // body
                .append(Doc::space())
                .append(item.block.to_doc().nest(2))
                .nest(2)
        }

        if let Item::Struct(item) = self {
            return match item.fields {
                Fields::Named(fields) => {
                    Doc::text("RecStructDef")
                        .append(parenthesize(
                            quote(Doc::text(format!("{}", item.ident)))
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // provenance variables
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            item.generics.lifetimes().map(|lft| {
                                                Doc::text(format!("\"{}\"", lft.lifetime.ident))
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
                                                            .append(field.ty.to_doc())
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
                            quote(Doc::text(format!("{}", item.ident)))
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // provenance variables
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            item.generics.lifetimes().map(|lft| {
                                                Doc::text(format!("\"{}\"", lft.lifetime.ident))
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
                                                    None => Some(field.ty.to_doc()),
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
                            quote(Doc::text(format!("{}", item.ident)))
                                .append(Doc::text(","))
                                .append(Doc::space())
                                // provenance variables
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            item.generics.lifetimes().map(|lft| {
                                                Doc::text(format!("\"{}\"", lft.lifetime.ident))
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
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        let mut stmts_backwards = self.stmts.clone().into_iter().rev().peekable();
        let init_acc = if let Some(Stmt::Semi(_, semi)) = stmts_backwards.peek() {
            parenthesize(
                semi.spans[0].to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(Doc::text("Prim"))
                    .append(Doc::space())
                    .append(Doc::text("Unit"))
                    .group()
            )
        } else if let Some(Stmt::Local(stmt)) = stmts_backwards.peek() {
            parenthesize(
                stmt.semi_token.spans[0].to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(Doc::text("Prim"))
                    .append(Doc::space())
                    .append(Doc::text("Unit"))
                    .group()
            )
        } else if let None = stmts_backwards.peek() {
            parenthesize(
                self.span().to_doc()
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
                Stmt::Local(mut stmt) => parenthesize(
                    stmt.span().to_doc()
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(Doc::text("Let"))
                        .append(Doc::space())
                        .append(parenthesize(
                            (if stmt.pats.len() == 1 {
                                stmt.pats.pop().unwrap().into_value().to_doc()
                            } else {
                                panic!("we don't support multiple patterns in a binding")
                            }).append(Doc::text(","))
                                .append(Doc::space())
                                .append(match stmt.ty {
                                    Some((_, ty)) => ty.to_doc(),
                                    None => panic!("types mut be fully-annotated"),
                                })
                                .append(Doc::text(","))
                                .append(Doc::space())
                                .append(match stmt.init {
                                    Some((_, expr)) =>
                                        Doc::text("(*=*)")
                                        .append(Doc::space())
                                        .append(parenthesize(expr.to_doc().nest(2))),
                                    None => panic!("we don't support uninitialized bindings"),
                                })
                                .append(Doc::text(","))
                                .append(Doc::space())
                                .append(acc)
                        ))
                ),
                Stmt::Expr(expr) => {
                    if acc == Doc::nil() {
                        parenthesize(expr.to_doc().nest(2))
                    } else {
                        parenthesize(expr.to_doc().nest(2))
                            .append(Doc::space())
                            .append(Doc::text(">>"))
                            .append(Doc::space())
                            .append(acc)
                    }
                },
                Stmt::Semi(expr, _) => parenthesize(
                    expr.to_doc()
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
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Pat::Ident(pat) = self {
            return Doc::text(format!("\"{}\"", pat.ident))
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for Type {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Type::Reference(ty) = self {
            let lft = match ty.lifetime.as_ref() {
                Some(lft) => lft,
                None => panic!("you need to include lifetime annotations in types!"),
            };
            return parenthesize(
                ty.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Ref")
                            .append(Doc::space())
                            .append(parenthesize(
                                parenthesize(
                                    lft.span().to_doc()
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        .append(quote(Doc::text(format!("{}", lft.ident)))))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(ty.mutability.to_doc())
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(parenthesize(ty.elem.to_doc()))
                            ))
                    )
            )
        }

        if let Type::Tuple(ty) = self {
            return parenthesize(
                ty.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(if ty.elems.is_empty() {
                        Doc::text("BaseTy")
                            .append(Doc::space())
                            .append(Doc::text("Unit"))
                            .group()
                    } else {
                        Doc::text("Tup")
                            .append(Doc::space())
                            .append(
                                Doc::text("[")
                                    .append(
                                        Doc::intersperse(
                                            ty.elems.into_iter().map(|ty| ty.to_doc()),
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

        if let Type::Path(ty) = self {
            let ty_name = ty.path.segments.iter().fold(
                String::new(),
                |mut acc, seg| {
                    acc.push_str(&format!("{}", seg.ident));
                    acc
                }
            );

            return parenthesize(
                ty.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(if ty_name == "u32" || ty_name == "usize" || ty_name == "isize" {
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
                        resolve_name(ty.path, true)
                    })
            )
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrintPlaceExpr for Expr {
    fn to_place_expr_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Expr::Path(expr) = self {
            return Doc::text("Var")
                .append(Doc::space())
                .append(quote(expr.path.to_doc()))
        }

        if let Expr::Field(expr) = self {
            return parenthesize(
                parenthesize(expr.base.to_place_expr_doc())
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

        self.to_doc()
    }
}

impl PrettyPrint for Expr {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Expr::Block(expr) = self {
            return parenthesize(expr.block.to_doc())
        }

        if let Expr::Group(expr) = self {
            return parenthesize(expr.expr.to_doc())
        }

        if let Expr::Lit(expr) = self {
            return expr.lit.to_doc()
        }

        if let Expr::Paren(expr) = self {
            return parenthesize(expr.expr.to_doc())
        }

        if let Expr::Reference(expr) = self {
            return parenthesize(
                expr.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Borrow")
                            .append(Doc::space())
                            .append(parenthesize(
                                parenthesize(expr.span().to_doc()
                                             .append(Doc::text(","))
                                             .append(Doc::space())
                                             .append(gensym()))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.mutability.to_doc())
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.expr.to_place_expr_doc())
                            ))
                            .group()
                    )
            )
        }

        if let Expr::Unary(expr) = self {
            return parenthesize(
                expr.op.to_doc()
                    .append(Doc::space())
                    .append(parenthesize(expr.expr.to_place_expr_doc()))
            )
        }

        if let Expr::Binary(expr) = self {
            return parenthesize(
                expr.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("BinOp")
                            .append(Doc::space())
                            .append(parenthesize(
                                expr.op.to_doc()
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.left.to_doc())
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.right.to_doc())
                            ))
                            .group()
                    )
            )
        }

        if let expr@Expr::Path(_) | expr@Expr::Field(_)  = self {
            return parenthesize(
                expr.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Move")
                            .append(Doc::space())
                            .append(parenthesize(expr.to_place_expr_doc()))
                            )
            )
        }

        if let Expr::Index(expr) = self {
            return parenthesize(
                expr.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(Doc::text("Idx")
                            .append(Doc::space())
                            .append(parenthesize(
                                expr.expr.to_doc()
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.index.to_doc())
                            ))
                            .group()
                    )
            )
        }

        if let Expr::Tuple(expr) = self {
            if expr.elems.is_empty() {
                return parenthesize(
                    expr.span().to_doc()
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
                    expr.span().to_doc()
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(Doc::text("Tup")
                                .append(Doc::space())
                                .append(
                                    Doc::text("[")
                                        .append(Doc::intersperse(
                                            expr.elems.into_iter().map(|expr| expr.to_doc()),
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
                expr.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Branch")
                            .append(Doc::space())
                            .append(parenthesize(
                                expr.cond.to_doc()
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.then_branch.to_doc())
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(match expr.else_branch {
                                        Some((_, els)) => els.to_doc(),
                                        None => parenthesize(
                                            expr.if_token.span().to_doc()
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
                expr.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Array")
                            .append(Doc::space())
                            .append(Doc::text("[")
                                    .append({
                                        Doc::intersperse(
                                            expr.elems.into_iter().map(|expr| expr.to_doc()),
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
                expr.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Array")
                            .append(Doc::space())
                            .append(Doc::text("[")
                                    .append({
                                        if let Expr::Lit(ExprLit { lit: Lit::Int(int), .. }) =
                                            *expr.len {
                                            let doc = parenthesize(expr.expr.to_doc());
                                            Doc::intersperse(
                                                (0..int.value()).map(|_| {
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
                expr.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Assign")
                            .append(Doc::space())
                            .append(parenthesize(
                                parenthesize(expr.left.to_place_expr_doc())
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(parenthesize(expr.right.to_doc()))
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
            }).to_doc()
        }

        if let Expr::While(expr) = self {
            return parenthesize(
                expr.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("While")
                            .append(Doc::space())
                            .append(parenthesize(
                                expr.cond.to_doc()
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .group()
                                    .nest(2)
                                    .append(parenthesize(expr.body.to_doc()))
                            ))
                            .group()
                    )
            )
        }

        if let Expr::ForLoop(expr) = self {
            return parenthesize(
                expr.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("For")
                            .append(Doc::space())
                            .append(parenthesize(
                                    expr.pat.to_doc()
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        .append(parenthesize(expr.expr.to_doc()))
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        .group()
                                        .nest(2)
                                        .append(parenthesize(expr.body.to_doc()))
                            ))
                            .group()
                    )
            )
        }

        if let Expr::Range(expr) = self {
            // we only support _finite_ ranges (by elaboration into an array)
            if let Some(Expr::Lit(ExprLit { lit: Lit::Int(n1), .. })) = expr.from.map(|x| *x) {
                if let Some(Expr::Lit(ExprLit { lit: Lit::Int(n2), .. })) = expr.to.map(|x| *x) {
                    return match expr.limits {
                        RangeLimits::HalfOpen(_) =>
                            Doc::intersperse(
                                (n1.value()..n2.value()).map(|n| Doc::text(format!("{}", n))),
                                Doc::text(";").append(Doc::space())
                            ),
                        RangeLimits::Closed(_) =>
                            Doc::intersperse(
                                (n1.value()..=n2.value()).map(|n| Doc::text(format!("{}", n))),
                                Doc::text(";").append(Doc::space())
                            ),
                    }
                } else {
                    panic!("we don't support non-literal or non-finite ranges")
                }
            } else {
                panic!("we don't support non-literal or non-finite ranges")
            }
        }

        if let Expr::Closure(expr) = self {
            return parenthesize(
                expr.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Fun")
                            .append(Doc::space())
                            .append(parenthesize(
                                Doc::text("[]")
                                    .append(Doc::space())
                                    .append(Doc::text("[]"))
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(
                                        Doc::intersperse(
                                            expr.inputs.into_iter().map(|arg| arg.to_doc()),
                                            Doc::text(";").append(Doc::space())
                                        )
                                    )
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(match expr.output {
                                        ReturnType::Default => Doc::text("None"),
                                        ReturnType::Type(_, ty) => Doc::text("Some")
                                            .append(Doc::space())
                                            .append(parenthesize(
                                                ty.span().to_doc()
                                                    .append(Doc::text(","))
                                                    .append(Doc::space())
                                                    .append(ty.to_doc())
                                            ))
                                            .group()
                                    })
                                    .append(Doc::text(","))
                                    .append(Doc::space())
                                    .append(expr.body.to_doc())
                            ))
                    )
            )
        }

        if let Expr::Macro(expr) = self {
            let macro_name = expr.mac.path.segments.iter().fold(
                String::new(),
                |mut acc, seg| {
                    acc.push_str(&format!("{}", seg.ident));
                    acc
                }
            );
            if macro_name == "abort" || macro_name == "panic" {
                return parenthesize(
                    expr.span().to_doc()
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(
                            Doc::text("Abort")
                                .append(Doc::space())
                                .append(match syn::parse2::<Lit>(expr.mac.tts) {
                                    Ok(lit) => lit.to_doc(),
                                    Err(_) => panic!("we don't support panic or \
                                                      aborts with non-literal arguments")
                                })
                                .group()
                        )
                );
            } else {
                panic!("we don't support macros besides abort! and panic!");
            }
        }

        if let Expr::Call(expr) = self {
            if let Expr::Path(func) = &*expr.func {
                let last_args1 = func.path.segments.last().unwrap().value().arguments.clone();
                let last_args2 = last_args1.clone();
                return parenthesize(
                    expr.span().to_doc()
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(
                            Doc::text("App")
                                .append(Doc::space())
                                .append(parenthesize(
                                    parenthesize(
                                        func.path.span().to_doc()
                                            .append(Doc::text(","))
                                            .append(Doc::space())
                                            .append(resolve_name(func.path.clone(), false))
                                    )
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        // provenance variable arguments
                                        .append(
                                            Doc::text("[")
                                                .append(last_args1.to_lifetime_generics_doc())
                                                .append(Doc::text("]"))
                                                .group()
                                        )
                                        .append(Doc::text(","))
                                        .append(Doc::space())
                                        // type variable arguments
                                        .append(
                                            Doc::text("[")
                                                .append(last_args2.to_type_generics_doc())
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
                                                            parenthesize(expr.to_doc())
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
            } else if let Expr::Closure(_) = *expr.func {
                return parenthesize(
                    expr.span().to_doc()
                        .append(Doc::text(","))
                        .append(Doc::space())
                        .append(
                            Doc::text("App")
                                .append(Doc::space())
                                .append(parenthesize(
                                    parenthesize(expr.func.to_doc())
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
                                                            parenthesize(expr.to_doc())
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
            } else {
                panic!("can't apply something other than an identifier or a closure")
            }
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for Path {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::intersperse(
            self.segments.into_iter().map(|seg| Doc::text(format!("{}", seg.ident))),
            Doc::text("::")
        )
    }
}

impl PrettyPrint for UnOp {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::text(match self {
            UnOp::Deref(_) => "Deref",
            UnOp::Not(_) => "Not",
            UnOp::Neg(_) => "Neg",
        })
    }
}

impl PrettyPrint for BinOp {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
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
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            Some(_) => Doc::text("Unique"),
            None => Doc::text("Shared"),
        }
    }
}

impl PrettyPrint for Lit {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Lit::Bool(bool) = self {
            return parenthesize(
                bool.span.to_doc()
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
                int.span().to_doc()
                    .append(Doc::text(","))
                    .append(Doc::space())
                    .append(
                        Doc::text("Prim")
                            .append(Doc::space())
                            .append(parenthesize(
                                Doc::text("Num")
                                    .append(Doc::space())
                                    .append(Doc::text(format!("{}", int.value())))
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
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            FnArg::Captured(cap) =>
                cap.pat.to_doc()
                .append(Doc::space())
                .append(Doc::text("@:"))
                .append(Doc::space())
                .append(parenthesize(cap.ty.to_doc()))
                .group(),
            _ => Doc::nil(),
        }
    }
}

impl PrettyPrint for LineColumn {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
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
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        parenthesize(
            quote(Doc::text(match self.source_file().path().file_name() {
                Some(name) => name.to_string_lossy().into_owned(),
                None => "unknown_file".to_owned(),
            }))
                .append(Doc::text(","))
                .append(Doc::space())
                .append(self.start().to_doc())
                .append(Doc::text(","))
                .append(Doc::space())
                .append(self.end().to_doc())
        )
    }

    #[cfg(not(procmacro2_semver_exempt))]
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        parenthesize(
            quote(Doc::text("unknown_file"))
                .append(Doc::text(","))
                .append(Doc::space())
                .append(self.start().to_doc())
                .append(Doc::text(","))
                .append(Doc::space())
                .append(self.end().to_doc())
        )
    }
}

trait PrettyPrintLifetimeGenerics {
    fn to_lifetime_generics_doc(self) -> Doc<'static, BoxDoc<'static, ()>>;
}

impl PrettyPrintLifetimeGenerics for PathArguments {
    fn to_lifetime_generics_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            PathArguments::None => Doc::nil(),
            PathArguments::Parenthesized(_) => Doc::text("(failwith \"unimplemented\")"),
            PathArguments::AngleBracketed(bracketed) => Doc::intersperse(
                bracketed.args.into_iter().filter(|arg| {
                    if let GenericArgument::Lifetime(_) = arg { true } else { false }
                }).map(|arg| match arg {
                    GenericArgument::Lifetime(lft) => parenthesize(
                        lft.span().to_doc()
                            .append(Doc::text(","))
                            .append(Doc::space())
                            .append(quote(Doc::text(format!("{}", lft.ident))))
                    ),
                    _ => unreachable!()
                }),
                Doc::text(";").append(Doc::space())
            )
        }
    }
}

trait PrettyPrintTypeGenerics {
    fn to_type_generics_doc(self) -> Doc<'static, BoxDoc<'static, ()>>;
}

impl PrettyPrintTypeGenerics for PathArguments {
    fn to_type_generics_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            PathArguments::None => Doc::nil(),
            PathArguments::Parenthesized(_) => Doc::text("(failwith \"unimplemented\")"),
            PathArguments::AngleBracketed(bracketed) => Doc::intersperse(
                bracketed.args.into_iter().filter(|arg| {
                    if let GenericArgument::Type(_) = arg { true } else { false }
                }).map(|arg| match arg {
                    GenericArgument::Type(typ) => typ.to_doc(),
                    _ => unreachable!()
                }),
                Doc::text(";").append(Doc::space())
            )
        }
    }
}
