use std::mem;
use std::mem::MaybeUninit;

/// Trait to extend iterables with `max_n` and `min_n`
pub trait MinMaxN<T: Ord> {
    fn max_n<const N: usize>(self) -> [Option<T>; N];
    fn min_n<const N: usize>(self) -> [Option<T>; N];

    fn min_n_all<const N: usize>(self) -> Option<[T; N]>
    where
        Self: Sized,
    {
        let src = self.min_n::<N>();
        let mut dst = [(); N].map(|_| MaybeUninit::uninit());
        for (d, s) in dst.iter_mut().zip(src) {
            d.write(s?);
        }

        // SAFETY:
        // we either initialized all elements (src and dst have the same length) or we returned (question mark operator)
        // in case 1, we can assume the entire array is init. In case two we don't run this code.
        Some(dst.map(|i| unsafe { i.assume_init() }))
    }

    fn max_n_all<const N: usize>(self) -> Option<[T; N]>
    where
        Self: Sized,
    {
        let src = self.max_n::<N>();
        let mut dst = [(); N].map(|_| MaybeUninit::uninit());
        for (d, s) in dst.iter_mut().zip(src) {
            d.write(s?);
        }

        // SAFETY:
        // we either initialized all elements (src and dst have the same length) or we returned (question mark operator)
        // in case 1, we can assume the entire array is init. In case two we don't run this code.
        Some(dst.map(|i| unsafe { i.assume_init() }))
    }

    fn max_n_iter<const N: usize>(self) -> MinMaxIter<T, N>
    where
        Self: Sized,
    {
        MinMaxIter(self.max_n(), 0)
    }

    fn min_n_iter<const N: usize>(self) -> MinMaxIter<T, N>
    where
        Self: Sized,
    {
        MinMaxIter(self.min_n(), 0)
    }
}

pub struct MinMaxIter<T, const N: usize>([Option<T>; N], usize);

impl<T, const N: usize> Iterator for MinMaxIter<T, N> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.1 >= self.0.len() {
            return None;
        }

        let res = self.0[self.1].take();
        self.1 += 1;
        res
    }
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
    /// Finds the `N` largest values in self
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
            if let Some(ref j) = res[res.len() - 1] {
                if i < *j {
                    continue;
                }
            }

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

    /// Finds the `N` smallest values in self
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
            if let Some(ref j) = res[res.len() - 1] {
                if i > *j {
                    continue;
                }
            }

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
    fn max_n_all_test() {
        let [a, b] = [1, 2, 3, 4].max_n_all().unwrap();
        assert_eq!(a, 4);
        assert_eq!(b, 3);
    }

    #[test]
    fn min_n_all_test() {
        let [a, b] = [1, 2, 3, 4].min_n_all().unwrap();
        assert_eq!(a, 1);
        assert_eq!(b, 2);
    }

    #[test]
    fn min_n_all_test_2() {
        assert!([1].min_n_all::<2>().is_none());
    }

    #[test]
    fn max_n_all_test_2() {
        assert!([1].max_n_all::<2>().is_none());
    }

    #[test]
    fn min_n_iter_test() {
        let mut res = [1, 2, 3, 4].min_n_iter::<2>();
        assert_eq!(res.next(), Some(1));
        assert_eq!(res.next(), Some(2));
        assert!(res.next().is_none())
    }

    #[test]
    fn max_n_iter_test() {
        let mut res = [1, 2, 3, 4].max_n_iter::<2>();
        assert_eq!(res.next(), Some(4));
        assert_eq!(res.next(), Some(3));
        assert!(res.next().is_none())
    }

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
