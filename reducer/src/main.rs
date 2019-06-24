use std::env;
use std::fs::File;
use std::io::Read;
use std::process;

use pretty::{BoxDoc, Doc};
use proc_macro2::{LineColumn, Span};
use syn::{Block, Expr, FnArg, GenericParam, Item, Lit, Member, Pat, Path, ReturnType, Stmt, Type};
use syn::{UnOp};
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

    let docs = syntax.items.into_iter().map(|item| {
        if let Item::Fn(inner) = item {
            Doc::text("(")
            // fn keyword and name
                .append(Doc::text("fn")
                        .append(Doc::space())
                        .append(Doc::text(format!("\"{}\"", inner.ident)))
                        .group()
                )
            // provenance variables
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(
                            Doc::intersperse(
                                inner.decl.generics.params.into_iter().flat_map(|param| match param {
                                    GenericParam::Lifetime(lft) => Some(
                                        Doc::text(format!("\"{}\"", lft.lifetime.ident))
                                    ),
                                    _ => None
                                }),
                                Doc::text(";").append(Doc::space()))
                        )
                        .append(Doc::text("]"))
                        .group()
                )
            // type variables
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(Doc::text("]"))
                        .group()
                )
            // parameters
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(
                            Doc::intersperse(
                                inner.decl.inputs.into_iter().map(|arg| match arg {
                                    FnArg::Captured(cap) =>
                                        cap.pat.to_doc()
                                        .append(Doc::space())
                                        .append(Doc::text("@:"))
                                        .append(Doc::space())
                                        .append(parenthesize(cap.ty.to_doc()))
                                        .group(),
                                    _ => Doc::nil(),
                                }),
                                Doc::text(";").append(Doc::space())
                            )
                        )
                        .append(Doc::text("]"))
                        .group()
                )
            // return type
                .append(Doc::space())
                .append(
                    parenthesize(match inner.decl.output {
                        ReturnType::Default => Doc::text("unit_ty"),
                        ReturnType::Type(_, ty) => ty.to_doc(),
                    })
                )
            // body
                .append(Doc::space())
                .append(inner.block.to_doc().nest(2))
                .append(")")
                .nest(2)
                .group()
        } else {
            Doc::nil()
        }
    });

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
                        .append(Doc::text("\"error: %a@. invalid global environment:@. %a@.\""))
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
        .group()
}

fn quote(doc: PP) -> PP {
    Doc::text("\"")
        .append(doc.group())
        .append(Doc::text("\""))
        .group()
}

trait PrettyPrint {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>>;
}

trait PrettyPrintPlaceExpr {
    fn to_place_expr_doc(self) -> Doc<'static, BoxDoc<'static, ()>>;
}

impl PrettyPrint for Block {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        parenthesize(Doc::intersperse(
            self.stmts.into_iter().map(|stmt| stmt.to_doc()),
            Doc::space()
        ))
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
            let lifetime = format!("{}", ty.lifetime.as_ref().unwrap().ident);
            return Doc::text("~&")
                .append(quote(Doc::text(lifetime)))
                .append(Doc::space())
                .append(ty.mutability.to_doc())
                .append(Doc::space())
                .append(parenthesize(ty.elem.to_doc()))
                .group()
        }

        if let Type::Tuple(ty) = self {
            return Doc::text("Tup")
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
        }

        if let Type::Path(ty) = self {
            return ty.path.to_doc()
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for Stmt {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Stmt::Local(mut stmt) = self {
            return Doc::text("letbe")
                .append(Doc::space())
                .append(stmt.span().to_doc())
                .append(Doc::space())
                .append(if stmt.pats.len() == 1 {
                    stmt.pats.pop().unwrap().into_value().to_doc()
                } else {
                    panic!("we don't support multiple patterns in a binding")
                })
                .append(Doc::space())
                .append(
                    match stmt.ty {
                        Some((_, ty)) => parenthesize(ty.span().to_doc()
                                                      .append(Doc::text(","))
                                                      .append(Doc::space())
                                                      .append(ty.to_doc())),
                        None => panic!("types must be fully-annotated")
                    }
                )
                .group()
                .append(Doc::space())
                .append(match stmt.init {
                    Some((_, expr)) =>
                        Doc::text("(*=*)")
                        .append(Doc::space())
                        .append(parenthesize(expr.to_doc().nest(2))),
                    None => panic!("we don't support uninitialized bindings")
                })
                .group()
        }

        if let Stmt::Expr(expr) = self {
            return parenthesize(expr.to_doc().nest(2))
        }

        if let Stmt::Semi(expr, semi) = self {
            return parenthesize(
                expr.to_doc()
                    .append(Doc::space())
                    .append(Doc::text(">>"))
                    .append(Doc::space())
                    .append(parenthesize(
                        semi.spans[0].to_doc()
                            .append(Doc::text(","))
                            .append(Doc::space())
                            .append(Doc::text("Prim"))
                            .append(Doc::space())
                            .append(Doc::text("Unit"))
                    ))
                    .nest(2)
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

        self.to_doc()
    }
}

impl PrettyPrint for Expr {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Expr::Block(expr) = self {
            return parenthesize(expr.block.to_doc())
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
                                gensym()
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

        if let expr@Expr::Path(_) = self {
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

        if let Expr::Tuple(expr) = self {
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

        if let Expr::Call(expr) = self {
            return parenthesize(
                expr.span().to_doc()
                .append(Doc::text(","))
                .append(Doc::space())
                .append(
                    Doc::text("App")
                        .append(Doc::space())
                        .append(
                            parenthesize(
                                Doc::text("~@@")
                                    .append(Doc::space())
                                    .append(parenthesize(expr.func.to_doc()))
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
                            )
                        )
                        .group()
                )
            )
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

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
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
