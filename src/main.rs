/// calc
///
/// A recursive descent parser for arithmetic expressions, with a symbol table.

use std::io;
use std::io::{Read, BufRead};
use std::collections::{VecDeque, BTreeMap};

fn main() {
    let stdin = io::stdin();
    let mut stdin = stdin.lock(); // Locking stdin gives us access to std::io::BufRead
    let mut calc = Calc::new(TokenStream::new(&mut stdin));
    calc.run_repl();
}

pub type CalcResult = Result<f64, SyntaxError>;

#[derive(Debug, PartialEq)]
pub enum SyntaxError {
    UnexpectedToken(TokenKind, Option<TokenKind>),
    InvalidToken(Option<Token>, String),
    UnknownSymbol(String),
}

pub struct Calc<'a> {
    ts: TokenStream<'a>,
    symtab: BTreeMap<String, f64>,
}

impl<'a> Calc<'a> {
    pub fn new(ts: TokenStream<'a>) -> Self {
        Calc {
            ts: ts,
            symtab: BTreeMap::new(),
        }
    }

    pub fn run_repl(&mut self) {
        while let Some(token) = self.ts.get() {
            match token.kind {
                TokenKind::Terminator | TokenKind::EOF => {
                    continue;
                }
                _ => {
                    self.ts.putback(token);
                    match self.statement() {
                        Ok(calculation) => {
                            println!("= {}", calculation);
                        }
                        Err(err) => {
                            println!("Error: {:?}", err);
                        }
                    }
                }
            }
        }
    }

    pub fn run(&mut self) -> CalcResult {
        let mut result: CalcResult = Ok(0.0);

        while let Some(token) = self.ts.get() {
            match token.kind {
                TokenKind::Terminator | TokenKind::EOF => {
                    continue;
                }
                _ => {
                    self.ts.putback(token);
                    result = Ok(self.statement()?);
                }
            }
        }

        result
    }

    pub fn define_symbol(&mut self, sym: String, val: f64) {
        self.symtab.insert(sym, val);
    }

    pub fn get_symbol(&self, sym: String) -> CalcResult {
        self.symtab.get(&sym).ok_or(SyntaxError::UnknownSymbol(sym)).map(|val| *val)
    }

    /// Statement = Declaration | Expression
    pub fn statement(&mut self) -> CalcResult {
        let token = self.ts.get().expect("statement() called out of order");
        let result;

        match token.kind {
            TokenKind::Let => result = self.declaration(),
            _ => {
                self.ts.putback(token);
                result = self.expression();
            }
        }

        result
    }

    /// Declaration = "let" Name "=" Expression
    /// "let" has already been consumed by Statement
    pub fn declaration(&mut self) -> CalcResult {
        let token = self.ts.get().expect("declaration() called out of order");

        if let TokenKind::Identifier = token.kind {
            let sym = token.name.expect("identifier token but no symbol name?");

            match self.ts.get() {
                Some(next) => {
                    if let TokenKind::Is = next.kind {
                        match self.expression() {
                            Ok(val) => {
                                self.define_symbol(sym, val);
                                return Ok(val);
                            }
                            Err(err) => {
                                return Err(err);
                            }
                        }
                    }

                    return Err(SyntaxError::UnexpectedToken(TokenKind::Is, Some(next.kind)));
                }
                _ => {
                    return Err(SyntaxError::UnexpectedToken(TokenKind::Is, None));
                }
            }
        }

        Err(SyntaxError::UnexpectedToken(TokenKind::Identifier, Some(token.kind)))
    }

    /// Expression = Term | Expression "+" Term | Expression "-" Term | Expression "%" Term
    pub fn expression(&mut self) -> CalcResult {
        self.term().and_then(|left| {
            let mut left = left;

            while let Some(token) = self.ts.get() {
                match token.kind {
                    TokenKind::Plus => left += self.term()?,
                    TokenKind::Minus => left -= self.term()?,
                    TokenKind::Modulo => left = left % self.term()?,
                    _ => {
                        self.ts.putback(token);
                        break;
                    }
                }
            }

            Ok(left)
        })
    }

    /// Term = Secondary | Term "*" Secondary | Term "/" Secondary
    pub fn term(&mut self) -> CalcResult {
        self.secondary().and_then(|left| {
            let mut left = left;

            while let Some(token) = self.ts.get() {
                match token.kind {
                    TokenKind::Multiply => left *= self.secondary()?,
                    TokenKind::Divide => {
                        match self.secondary() {
                            Ok(0.0) => {
                                return Err(SyntaxError::InvalidToken(Some(token),
                                                                     "Divide by zero".to_string()));
                            }
                            Ok(val) => {
                                left /= val;
                            }
                            Err(err) => {
                                return Err(err);
                            }
                        }
                    }
                    _ => {
                        self.ts.putback(token);
                        break;
                    }
                }
            }

            Ok(left)
        })
    }

    pub fn naive_factorial(&self, n: f64) -> Result<f64, String> {
        if n.floor() != n || n < 0.0 {
            return Err("Factorial is only valid on the natural numbers (0, 1, 2, ... n)"
                .to_string());
        }

        if n == 0.0 {
            return Ok(1.0);
        }

        let mut val: f64 = 1.0;
        for i in 1..((n + 1.0) as usize) {
            val *= i as f64;
        }

        Ok(val)
    }

    /// Secondary = Primary | Primary "!" | Primary "^" Primary
    pub fn secondary(&mut self) -> CalcResult {
        self.primary().and_then(|left| {
            let mut left = left;
            while let Some(token) = self.ts.get() {
                match token.kind {
                    TokenKind::Factorial => {
                        match self.naive_factorial(left) {
                            Ok(factorial) => left = factorial,
                            Err(msg) => {
                                return Err(SyntaxError::InvalidToken(None, msg));
                            }
                        }
                    }
                    TokenKind::Exponent => left = left.powf(self.primary()?),
                    _ => {
                        self.ts.putback(token);
                        break;
                    }
                }
            }

            Ok(left)
        })
    }

    /// Primary = "(" Expression ")" | Identifier | "-" Primary | "+" Primary | Number
    pub fn primary(&mut self) -> CalcResult {
        let token = self.ts.get().expect("primary() called out of order");
        match token.kind {
            TokenKind::LParen => {
                let expr = self.expression()?;
                // Look for closing parentheses
                self.ts
                    .get()
                    .ok_or(SyntaxError::UnexpectedToken(TokenKind::LParen, None))
                    .and_then(|token| {
                        match token.kind {
                            TokenKind::RParen => Ok(expr),
                            _ => {
                                Err(SyntaxError::UnexpectedToken(TokenKind::RParen,
                                                                 Some(token.kind)))
                            }
                        }
                    })
            }
            TokenKind::Identifier => self.get_symbol(token.name.unwrap()),
            TokenKind::Minus => self.primary().map(|val| -val),
            TokenKind::Plus => self.primary(),
            TokenKind::Number => Ok(token.value.expect("There should've been a value here")),
            _ => {
                let msg = format!("Expected a number, identifier or parenthetical expression, \
                                   but got {:?}",
                                  token.kind);
                Err(SyntaxError::InvalidToken(Some(token), msg))
            }
        }
    }
}


#[derive(Debug, PartialEq)]
pub enum TokenKind {
    Divide,
    EOF,
    Exponent,
    Factorial,
    Identifier,
    Is,
    LParen,
    Let,
    Minus,
    Modulo,
    Multiply,
    Number,
    Plus,
    RParen,
    Sqrt,
    Terminator,
    Times,
}

#[derive(Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub value: Option<f64>,
    pub name: Option<String>,
}

pub struct TokenStream<'a> {
    source: &'a mut BufRead,
    stream: VecDeque<Token>,
    current_token: Option<String>,
}

impl<'a> TokenStream<'a> {
    pub fn new(source: &'a mut BufRead) -> Self {
        TokenStream {
            source: source,
            stream: VecDeque::new(),
            current_token: None,
        }
    }

    /// Get the next token. If there are no tokens ready, parse the input for more.  If the file is
    /// EOF, return None
    pub fn get(&mut self) -> Option<Token> {
        let token = self.stream.pop_front().or_else(|| {
            self.parse_line();
            self.stream.pop_front().map(|token| token)
        });
        token
    }


    /// Push a token to the front of the stream.
    /// The token need never have been in the stream.
    pub fn putback(&mut self, token: Token) {
        self.stream.push_front(token);
    }

    pub fn parse_line(&mut self) {
        let mut buf = String::new();

        if let 0 = self.source.read_line(&mut buf).expect("i/o failure") {
            return;
        }

        self.tokenize(&buf);
    }

    pub fn tokenize(&mut self, tokensource: &str) {
        for c in tokensource.chars() {
            match c {
                ';' | '\n' => self.finish_token(Some(TokenKind::Terminator)),
                '+' => self.finish_token(Some(TokenKind::Plus)),
                '-' => self.finish_token(Some(TokenKind::Minus)),
                '*' => self.finish_token(Some(TokenKind::Multiply)),
                '/' => self.finish_token(Some(TokenKind::Divide)),
                '%' => self.finish_token(Some(TokenKind::Modulo)),
                '!' => self.finish_token(Some(TokenKind::Factorial)),
                '^' => self.finish_token(Some(TokenKind::Exponent)),
                '=' => self.finish_token(Some(TokenKind::Is)),
                '(' => self.finish_token(Some(TokenKind::LParen)),
                ')' => self.finish_token(Some(TokenKind::RParen)),
                // See https://gist.github.com/Dethnull/9613129 to get a better list of utf-8
                // whitespace characters
                ' ' | '\r' | '\t' => self.finish_token(None),
                _ => {
                    // This feels unnatural but it pleased the borrow checker
                    if self.current_token.is_some() {
                        self.current_token.as_mut().unwrap().push(c);
                    } else {
                        self.current_token = Some(c.to_string());
                    }
                }
            }
        }

        self.finish_token(Some(TokenKind::EOF));
    }

    pub fn add_token(&mut self, kind: TokenKind, value: Option<f64>, name: Option<String>) {
        self.stream.push_back(Token {
            kind: kind,
            value: value,
            name: name,
        });
    }

    pub fn finish_token(&mut self, terminator: Option<TokenKind>) {
        let token = self.current_token.take();

        if token.is_some() {
            let token = token.unwrap();

            match token.as_ref() {
                "let" => {
                    self.add_token(TokenKind::Let, None, None);
                }
                "sqrt" => {
                    self.add_token(TokenKind::Sqrt, None, None);
                }
                _ => {
                    match token.chars().nth(0).unwrap() {
                        '0'...'9' => {
                            let value: f64 = token.parse()
                                .expect(&format!("Not a valid f64: {}", token));

                            self.add_token(TokenKind::Number, Some(value), None);
                        }
                        _ => {
                            self.add_token(TokenKind::Identifier, None, Some(token));
                        }
                    }
                }
            }
        }

        if terminator.is_some() {
            let terminator = terminator.unwrap();
            self.add_token(terminator, None, None);
        }
    }
}

pub struct StringReader {
    string: String,
    cursor: usize,
}

/// An implementation of the Read trait for Strings to test TokenStream without needing a file.
impl StringReader {
    pub fn new(string: String) -> Self {
        StringReader {
            string: string.clone(),
            cursor: 0,
        }
    }
}

impl Read for StringReader {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let bytes = self.string.as_bytes();

        let remaining = bytes.len() - self.cursor;
        let buflen = buf.len();
        let readsize = if remaining < buflen {
            remaining
        } else {
            buflen
        };

        for i in 0..readsize {
            buf[i] = bytes[self.cursor];
            self.cursor += 1;
        }

        Ok(readsize as usize)
    }
}


#[cfg(test)]
mod test {
    use std::io::{Read, BufReader};
    use super::{StringReader, TokenStream, TokenKind, Token, Calc, CalcResult, SyntaxError};

    #[test]
    fn string_reader_test() {
        let s = "yo yo what up yo, time is running out";
        let s_string = s.to_string();
        let mut sreader = StringReader::new(s_string.clone());
        let mut buf: [u8; 8] = [0; 8];

        assert_eq!(sreader.read(&mut buf).unwrap(), 8 as usize);
        assert_eq!(buf[0..8], s.as_bytes()[0..8]);
        assert_eq!(sreader.read(&mut buf).unwrap(), 8 as usize);
        assert_eq!(buf[0..8], s.as_bytes()[8..16]);
        assert_eq!(sreader.read(&mut buf).unwrap(), 8 as usize);
        assert_eq!(buf[0..8], s.as_bytes()[16..24]);
        assert_eq!(sreader.read(&mut buf).unwrap(), 8 as usize);
        assert_eq!(buf[0..8], s.as_bytes()[24..32]);
        assert_eq!(sreader.read(&mut buf).unwrap(), 5 as usize);
        assert_eq!(buf[0..5], s.as_bytes()[32..37]);

        let mut sreader = StringReader::new(s_string.clone());
        let mut stringbuf = String::new();
        assert_eq!(sreader.read_to_string(&mut stringbuf).unwrap(),
                   s_string.len());
        assert_eq!(s_string, stringbuf);
    }

    #[test]
    fn tokenstream_tests() {
        let kant = "5 + 7;".to_string();

        let mut kantbuf = BufReader::new(StringReader::new(kant));
        let mut ts = TokenStream::new(&mut kantbuf);
        assert_eq!(ts.get(),
                   Some(Token {
                       kind: TokenKind::Number,
                       value: Some(5.0),
                       name: None,
                   }));

        assert_eq!(ts.get(),
                   Some(Token {
                       kind: TokenKind::Plus,
                       value: None,
                       name: None,
                   }));

        assert_eq!(ts.get(),
                   Some(Token {
                       kind: TokenKind::Number,
                       value: Some(7.0),
                       name: None,
                   }));

        assert_eq!(ts.get(),
                   Some(Token {
                       kind: TokenKind::Terminator,
                       value: None,
                       name: None,
                   }));

        assert_eq!(ts.get(),
                   Some(Token {
                       kind: TokenKind::EOF,
                       value: None,
                       name: None,
                   }));

        assert_eq!(ts.get(), None);
    }

    #[test]
    fn calc_tests() {
        assert_eq!(calculate("7 + 5;"), Ok(12.0));
        assert_eq!(calculate("7 * 3 + 5;"), Ok(26.0));
        assert_eq!(calculate(";;;;;;;;;;;;;;;;;;;;;;;;;;7 * 3 + 5;;;;;;;;;;;;;;;;;;;;;;;;;;;;"),
                   Ok(26.0));
        assert_eq!(calculate("7 * 3 + 5"), Ok(26.0));
        assert_eq!(calculate("7 * (3 + 5)"), Ok(56.0));
        assert_eq!(calculate("((((((((((((((((((((((((((((((((((((((7/2 * \
                              10))))))))))))))))))))))))))))))))))))))"),
                   Ok(35.0));
        assert_eq!(calculate("let a = 5; let b = ((7/2 * 10) / a)-a-a-a; b;"),
                   Ok(-8.0));
        assert_eq!(calculate("5 % 2"), Ok(1.0));
        assert_eq!(calculate("+31337"), Ok(31337.0));
        assert_eq!(calculate("-31337"), Ok(-31337.0));
        assert_eq!(calculate("0.25^2"), Ok(0.0625));
        assert_eq!(calculate("1*2*3*4*5*6*7*8*9"), Ok(362880.0));
        assert_eq!(calculate("(0.2+0.05)^2"), Ok(0.0625));
    }

    #[test]
    fn error_tests() {
        assert_eq!(calculate("a"),
                   Err(SyntaxError::UnknownSymbol("a".to_string())));
    }

    #[test]
    fn factorial_tests() {
        assert_eq!(calculate("(2^3)!"), Ok(40320.0));
        assert_eq!(calculate("2!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"), Ok(2.0));
        assert_eq!(calculate("3!!"), Ok(720.0));
        assert_eq!(calculate("0!"), Ok(1.0));
        assert_eq!(calculate("1!"), Ok(1.0));
        assert_eq!(calculate("2!"), Ok(2.0));
        assert_eq!(calculate("3!"), Ok(6.0));
        assert_eq!(calculate("4!"), Ok(24.0));
        assert_eq!(calculate("5!"), Ok(120.0));
        assert_eq!(calculate("6!"), Ok(720.0));
        assert_eq!(calculate("7!"), Ok(5040.0));
        assert_eq!(calculate("8!"), Ok(40320.0));
        assert_eq!(calculate("9!"), Ok(362880.0));
        assert_eq!(calculate("10!"), Ok(3628800.0));
        assert_eq!(calculate("11!"), Ok(39916800.0));
        assert_eq!(calculate("12!"), Ok(479001600.0));
        assert_eq!(calculate("13!"), Ok(6227020800.0));
        assert_eq!(calculate("14!"), Ok(87178291200.0));
        assert_eq!(calculate("15!"), Ok(1307674368000.0));
        assert_eq!(calculate("16!"), Ok(20922789888000.0));
        assert_eq!(calculate("17!"), Ok(355687428096000.0));
        assert_eq!(calculate("18!"), Ok(6402373705728000.0));
        assert_eq!(calculate("19!"), Ok(121645100408832000.0));
        assert_eq!(calculate("20!"), Ok(2432902008176640000.0));
        assert_eq!(calculate("25!"), Ok(15511210043330985984000000.0));
        assert_eq!(calculate("26!"), Ok(403291461126605635584000000.0));
        assert_eq!(calculate("27!"), Ok(10888869450418352160768000000.0));

        // 27! seems to be the limit for properly calculated factorials with rust's f64
        // assert_eq!(calculate("28!"), Ok(304888344611713860501504000000.0));
        // assert_eq!(calculate("29!"), Ok(8841761993739701954543616000000.0));
        // assert_eq!(calculate("30!"), Ok(265252859812191058636308480000000.0));
    }

    fn calculate(stmt: &str) -> CalcResult {
        let stmt_str = stmt.to_string();
        let mut buf = BufReader::new(StringReader::new(stmt_str));
        let mut calculator = Calc::new(TokenStream::new(&mut buf));

        calculator.run()
    }
}
