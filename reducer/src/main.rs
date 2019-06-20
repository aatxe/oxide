use std::env;
use std::fs::File;
use std::io::Read;
use std::process;

use pretty::{BoxDoc, Doc};
use syn::{Block, Expr, FnArg, GenericParam, Item, Member, Pat, Path, ReturnType, Stmt, Type};

type PP = Doc<'static, BoxDoc<'static, ()>>;

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

    for item in syntax.items.into_iter() {
        if let Item::Fn(inner) = item {
            let doc: Doc<BoxDoc<()>> =
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
                                    FnArg::Captured(cap) => {
                                        if let Pat::Ident(id) = cap.pat {
                                            Doc::text(format!("\"{}\"", id.ident))
                                                .append(Doc::space())
                                                .append(Doc::text("@:"))
                                                .append(Doc::space())
                                                .append(Doc::text("("))
                                                .append(cap.ty.to_doc())
                                                .append(Doc::text(")"))
                                                .group()
                                        } else {
                                            Doc::nil()
                                        }
                                    }
                                    _ => { Doc::nil() }
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
                        ReturnType::Default => Doc::text("unit"),
                        ReturnType::Type(_, ty) => ty.to_doc(),
                    })
                )
                // body
                .append(Doc::space())
                .append(inner.block.to_doc())
                .append(")")
                .group();
            let mut buf = Vec::new();
            doc.render(100, &mut buf).unwrap();
            println!("{}", String::from_utf8(buf).unwrap());
        }
    }

    // println!("{:#?}", syntax);
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

impl PrettyPrint for Block {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::intersperse(
            self.stmts.into_iter().map(|stmt| {
                parenthesize(stmt.to_doc())
            }),
            Doc::space().append(Doc::text(">>")).append(Doc::space())
        )
    }
}

impl PrettyPrint for Type {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Type::Reference(rf) = self {
            let lifetime = format!("{}", rf.lifetime.as_ref().unwrap().ident);
            return Doc::text("~&")
                .append(
                    Doc::text("\"")
                        .append(Doc::text(lifetime))
                        .append("\"")
                        .group()
                )
                .append(Doc::space())
                .append(
                    match rf.mutability {
                        Some(_) => Doc::text("uniq"),
                        None => Doc::text("shrd")
                    }
                )
                .append(Doc::space())
                .append(rf.elem.to_doc())
                .group()
        }

        if let Type::Tuple(tup) = self {
            return Doc::text("Tup")
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(
                            Doc::intersperse(
                                tup.elems.into_iter().map(|ty| ty.to_doc()),
                                Doc::text(";").append(Doc::space())
                            )
                        )
                        .append(Doc::text("]"))
                        .group()
                )
                .group()
        }

        if let Type::Path(path) = self {
            return path.path.to_doc()
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for Stmt {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {

        if let Stmt::Expr(expr) = self {
            return expr.to_doc()
        }

        if let Stmt::Semi(expr, _) = self {
            return expr.to_doc()
                .append(Doc::space())
                .append(Doc::text(">>"))
                .append(Doc::space())
                .append("unit")
                .group()
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for Expr {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Expr::Block(block) = self {
            return parenthesize(block.block.to_doc())
        }

        if let Expr::Paren(paren) = self {
            return parenthesize(paren.expr.to_doc())
        }

        if let Expr::Reference(borrow) = self {
            return Doc::text("borrow")
                .append(Doc::space())
                .append(borrow.mutability.to_doc())
                .append(Doc::space())
                .append(borrow.expr.to_doc())
                .group()
        }

        if let Expr::Path(path) = self {
            return Doc::text("Var")
                .append(Doc::space())
                .append(quote(path.path.to_doc()))
        }

        if let Expr::Field(field) = self {
            return parenthesize(
                parenthesize(field.base.to_doc())
                    .append(Doc::space())
                    .append(match field.member {
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

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for Path {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::intersperse(
            self.segments.into_iter().map(|seg| {
                Doc::text(format!("{}", seg.ident))
            }), Doc::text("::")
        )
    }
}

impl PrettyPrint for Option<syn::token::Mut> {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            Some(_) => Doc::text("uniq"),
            None => Doc::text("shrd"),
        }
    }
}
