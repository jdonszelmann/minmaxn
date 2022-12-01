use std::mem;

pub trait MinMaxN<T: Ord> {
    fn max_n<const N: usize>(self) -> [Option<T>; N];
    fn min_n<const N: usize>(self) -> [Option<T>; N];
}

fn ilog2(mut num: usize) -> usize {
    let mut res = 0;

    while {
        num >>= 1;
        num != 0
    } {
        res += 1;
    }

    res
}

impl<T, U> MinMaxN<T> for U
where
    U: IntoIterator<Item = T>,
    T: Ord,
{
    fn max_n<const N: usize>(self) -> [Option<T>; N] {
        let iter = self.into_iter();
        let size_hint = iter.size_hint().0;
        let mut res = [(); N].map(|_| None);

        if size_hint != 0 && N > ilog2(iter.size_hint().0) as usize {
            let mut items = iter.collect::<Vec<_>>();
            items.sort();

            for (src, dst) in items.into_iter().rev().zip(&mut res) {
                *dst = Some(src);
            }

            return res;
        }

        for mut i in iter {
            for j in &mut res {
                if let Some(j) = j {
                    if i > *j {
                        i = mem::replace(j, i);
                    }
                } else {
                    *j = Some(i);
                    break;
                }
            }
        }

        res
    }

    fn min_n<const N: usize>(self) -> [Option<T>; N] {
        let iter = self.into_iter();
        let size_hint = iter.size_hint().0;
        let mut res = [(); N].map(|_| None);

        if size_hint != 0 && N > ilog2(iter.size_hint().0) as usize {
            let mut items = iter.collect::<Vec<_>>();
            items.sort();

            for (src, dst) in items.into_iter().zip(&mut res) {
                *dst = Some(src);
            }

            return res;
        }

        for mut i in iter {
            for j in &mut res {
                if let Some(j) = j {
                    if i < *j {
                        i = mem::replace(j, i);
                    }
                } else {
                    *j = Some(i);
                    break;
                }
            }
        }

        res
    }
}

#[cfg(test)]
mod tests {
    use super::MinMaxN;
    use crate::ilog2;

    #[test]
    fn max_n_test() {
        let [a, b] = [1, 2, 3, 4].max_n();
        assert_eq!(a, Some(4));
        assert_eq!(b, Some(3));
    }

    #[test]
    fn max_n_test_2() {
        let [a, b, c, d] = [1, 2, 3, 4].max_n();
        assert_eq!(a, Some(4));
        assert_eq!(b, Some(3));
        assert_eq!(c, Some(2));
        assert_eq!(d, Some(1));
    }

    #[test]
    fn max_n_test_3() {
        let [a, b, c, d, e] = [1, 2, 3, 4].max_n();
        assert_eq!(a, Some(4));
        assert_eq!(b, Some(3));
        assert_eq!(c, Some(2));
        assert_eq!(d, Some(1));
        assert_eq!(e, None);
    }

    #[test]
    fn max_n_test_4() {
        let [a, b] = [1, 1, 1, 1, 1, 1, 1].max_n();
        assert_eq!(a, Some(1));
        assert_eq!(b, Some(1));
    }

    #[test]
    fn max_n_test_5() {
        let [a, b] = [5, 4, 3, 2, 1].max_n();
        assert_eq!(a, Some(5));
        assert_eq!(b, Some(4));
    }

    #[test]
    fn min_n_test() {
        let [a, b] = [1, 2, 3, 4].min_n();
        assert_eq!(a, Some(1));
        assert_eq!(b, Some(2));
    }

    #[test]
    fn min_n_test_2() {
        let [a, b, c, d] = [1, 2, 3, 4].min_n();
        assert_eq!(a, Some(1));
        assert_eq!(b, Some(2));
        assert_eq!(c, Some(3));
        assert_eq!(d, Some(4));
    }

    #[test]
    fn min_n_test_3() {
        let [a, b, c, d, e] = [1, 2, 3, 4].min_n();
        assert_eq!(a, Some(1));
        assert_eq!(b, Some(2));
        assert_eq!(c, Some(3));
        assert_eq!(d, Some(4));
        assert_eq!(e, None);
    }

    #[test]
    fn min_n_test_4() {
        let [a, b] = [1, 1, 1, 1, 1, 1, 1].min_n();
        assert_eq!(a, Some(1));
        assert_eq!(b, Some(1));
    }

    #[test]
    fn min_n_test_5() {
        let [a, b] = [5, 4, 3, 2, 1].min_n();
        assert_eq!(a, Some(1));
        assert_eq!(b, Some(2));
    }

    #[test]
    fn ilog2_test() {
        assert_eq!(ilog2(2), 1);
        assert_eq!(ilog2(4), 2);
        assert_eq!(ilog2(32), 5);
    }
}
