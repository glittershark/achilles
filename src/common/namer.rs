use std::fmt::Display;
use std::marker::PhantomData;

pub struct Namer<T, F> {
    make_name: F,
    counter: u64,
    _phantom: PhantomData<T>,
}

impl<T, F> Namer<T, F> {
    pub fn new(make_name: F) -> Self {
        Namer {
            make_name,
            counter: 0,
            _phantom: PhantomData,
        }
    }
}

impl Namer<String, Box<dyn Fn(u64) -> String>> {
    pub fn with_prefix<T>(prefix: T) -> Self
    where
        T: Display + 'static,
    {
        Namer::new(move |i| format!("{}{}", prefix, i)).boxed()
    }

    pub fn with_suffix<T>(suffix: T) -> Self
    where
        T: Display + 'static,
    {
        Namer::new(move |i| format!("{}{}", i, suffix)).boxed()
    }

    pub fn alphabetic() -> Self {
        Namer::new(|i| {
            if i <= 26 {
                std::char::from_u32((i + 96) as u32).unwrap().to_string()
            } else {
                format!(
                    "{}{}",
                    std::char::from_u32(((i % 26) + 96) as u32).unwrap(),
                    i - 26
                )
            }
        })
        .boxed()
    }
}

impl<T, F> Namer<T, F>
where
    F: Fn(u64) -> T,
{
    pub fn make_name(&mut self) -> T {
        self.counter += 1;
        (self.make_name)(self.counter)
    }

    pub fn boxed(self) -> NamerOf<T>
    where
        F: 'static,
    {
        Namer {
            make_name: Box::new(self.make_name),
            counter: self.counter,
            _phantom: self._phantom,
        }
    }

    pub fn map<G, U>(self, f: G) -> NamerOf<U>
    where
        G: Fn(T) -> U + 'static,
        T: 'static,
        F: 'static,
    {
        Namer {
            counter: self.counter,
            make_name: Box::new(move |x| f((self.make_name)(x))),
            _phantom: PhantomData,
        }
    }
}

pub type NamerOf<T> = Namer<T, Box<dyn Fn(u64) -> T>>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prefix() {
        let mut namer = Namer::with_prefix("t");
        assert_eq!(namer.make_name(), "t1");
        assert_eq!(namer.make_name(), "t2");
    }

    #[test]
    fn suffix() {
        let mut namer = Namer::with_suffix("t");
        assert_eq!(namer.make_name(), "1t");
        assert_eq!(namer.make_name(), "2t");
    }

    #[test]
    fn alphabetic() {
        let mut namer = Namer::alphabetic();
        assert_eq!(namer.make_name(), "a");
        assert_eq!(namer.make_name(), "b");
        (0..25).for_each(|_| {
            namer.make_name();
        });
        assert_eq!(namer.make_name(), "b2");
    }

    #[test]
    fn custom_callback() {
        let mut namer = Namer::new(|n| n + 1);
        assert_eq!(namer.make_name(), 2);
        assert_eq!(namer.make_name(), 3);
    }
}
