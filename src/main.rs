use std::io;
use std::io::{Read, BufRead};
use std::collections::{VecDeque, BTreeMap};

fn main() {
    let stdin = io::stdin();
    let mut stdin = stdin.lock(); // Locking stdin gives us access to std::io::BufRead
    let mut calc = Calc::new(TokenStream::new(&mut stdin), BTreeMap::new());
    calc.run_repl();
}

pub struct Calc<'a> {
    ts: TokenStream<'a>,
    symtab: BTreeMap<String, f64>,
}

impl<'a> Calc<'a> {
    pub fn new(ts: TokenStream<'a>, symtab: BTreeMap<String, f64>) -> Self {
        Calc {
            ts: ts,
            symtab: symtab,
        }
    }

    pub fn run_repl(&mut self) {
        while let Some(token) = self.ts.get() {
            match token.kind {
                TokenKind::Terminator => {
                    continue;
                }
                _ => {
                    self.ts.putback(token);
                    match self.statement() {
                        Ok(calculation) => {
                            println!("= {}", calculation);
                        }
                        Err(msg) => {
                            println!("Error: {}", msg);
                        }
                    }
                }
            }
        }
    }

    pub fn run(&mut self) -> Result<f64, String> {
        let mut result: Result<f64, String> = Ok(0.0);

        while let Some(token) = self.ts.get() {
            match token.kind {
                TokenKind::Terminator => {
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

    pub fn get_symbol(&self, sym: String) -> Result<f64, String> {
        self.symtab.get(&sym).ok_or(format!("No such symbol '{}' defined", sym)).map(|val| *val)
    }

    /**
     * Statement = Declaration | Expression
     */
    pub fn statement(&mut self) -> Result<f64, String> {
        let token = self.ts.get().expect("statement() called out of order");

        match token.kind {
            TokenKind::Let => self.declaration(),
            _ => {
                self.ts.putback(token);
                self.expression()
            }
        }
    }

    /**
     * Declaration = "let" Name "=" Expression
     *
     * Let has already been consumed by Statement
     */
    pub fn declaration(&mut self) -> Result<f64, String> {
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
                            Err(msg) => {
                                return Err(msg);
                            }
                        }
                    }

                    return Err(format!("Expected '=', found {:?}", next.kind));
                }
                _ => {
                    return Err(format!("Expected '=', found nothing"));
                }
            }
        }

        Err(format!("Expected identifier, found {:?}", token.kind))
    }

    /**
     * Expression = Term | Expression "+" Term | Expression "-" Term | Expression "%" Term
     */
    pub fn expression(&mut self) -> Result<f64, String> {
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

    /**
     * Term = Secondary | Term "*" Secondary | Term "/" Secondary 
     */
    pub fn term(&mut self) -> Result<f64, String> {
        self.secondary().and_then(|left| {
            let mut left = left;

            while let Some(token) = self.ts.get() {
                match token.kind {
                    TokenKind::Multiply => left *= self.secondary()?, 
                    TokenKind::Divide => {
                        match self.secondary() {
                            Ok(0.0) => {
                                return Err("Divide by zero".to_string());
                            }
                            Ok(val) => {
                                left /= val;
                            }
                            Err(msg) => {
                                return Err(msg);
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

    pub fn factorial(&self, n: f64) -> Result<f64, String> {
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

    pub fn secondary(&mut self) -> Result<f64, String> {
        self.primary().and_then(|left| {
            let mut left = left;
            while let Some(token) = self.ts.get() {
                match token.kind {
                    TokenKind::Factorial => left = self.factorial(left)?,
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

    pub fn primary(&mut self) -> Result<f64, String> {
        let token = self.ts.get().expect("Primary called out of order");

        match token.kind {
            TokenKind::LParen => {
                let expr = self.expression()?;
                // Look for closing parentheses
                self.ts
                    .get()
                    .ok_or("Expected ')', found nothing".to_string())
                    .and_then(|token| {
                        match token.kind {
                            TokenKind::RParen => Ok(expr),
                            _ => Err(format!("Expected ')', but found {:?}", token.kind)),
                        }
                    })
            }
            TokenKind::Identifier => self.get_symbol(token.name.unwrap()),
            TokenKind::Minus => self.primary().map(|val| -val),
            TokenKind::Number => Ok(token.value.expect("There should've been a value here")),
            _ => Err(format!("Expected a number, but got {:?}", token.kind)),
        }
    }
}


#[derive(Debug)]
pub enum TokenKind {
    Divide,
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
    Terminator,
    Times,
}

#[derive(Debug)]
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

    /**
     * Get the next token. If there are no tokens ready, parse the input for more.  If the file is
     * EOF, return None
     */
    pub fn get(&mut self) -> Option<Token> {
        self.stream.pop_front().or_else(|| {
            self.parse_line();
            self.stream.pop_front().map(|token| token)
        })
    }

    /**
     * Push a token to the front of the stream.
     * The token need never have been in the stream.
     */
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

            if token == "let" {
                self.add_token(TokenKind::Let, None, None);
            } else {
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

        if terminator.is_some() {
            self.add_token(terminator.unwrap(), None, None);
        }
    }
}

pub struct StringReader {
    string: String,
    cursor: usize,
}

// An implementation of the Read trait for Strings to test TokenStream without needing a file.
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
    use std::io::Read;
    use super::{StringReader, TokenStream, TokenKind, Token, Calc};

    #[test]
    fn string_reader_test() {
        let s = "yo yo what up yo, time is running out";
        let mut sreader = StringReader::new(s.to_string());
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
    }

    #[test]
    fn tokenstream_tests() {}
}
