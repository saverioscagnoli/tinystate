pub trait States: Sized + Clone {
    type Tag: Copy + Eq + 'static;
    const COUNT: usize;
    const NAMES: &'static [&'static str];
    const TAGS: &'static [Self::Tag];

    fn tag(&self) -> Self::Tag;
    fn tag_index(tag: Self::Tag) -> usize;

    fn index(&self) -> usize {
        Self::tag_index(self.tag())
    }

    fn name(&self) -> &'static str {
        Self::NAMES[self.index()]
    }
}

pub trait Events: Sized {
    type Tag: Copy + Eq + 'static;
    const COUNT: usize;
    const NAMES: &'static [&'static str];
    const TAGS: &'static [Self::Tag];

    fn tag(&self) -> Self::Tag;
    fn tag_index(tag: Self::Tag) -> usize;

    fn index(&self) -> usize {
        Self::tag_index(self.tag())
    }

    fn name(&self) -> &'static str {
        Self::NAMES[self.index()]
    }
}
