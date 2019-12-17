fn unnest<'a, 'b>(pt: &'a mut &'b mut u32) -> &'a mut u32 {
    &mut **pt
}
