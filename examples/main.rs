use std::borrow::Cow;
use vmem::{AllocStrategy, Vmem};

static KERNEL_HEAP_ARENA: Vmem = Vmem::new(Cow::Borrowed("kmem_default_arena"), 1, None);

fn main() {
    pretty_env_logger::init();

    let arena = &KERNEL_HEAP_ARENA;

    unsafe {
        use core::ptr;
        use libc::{mmap, MAP_ANON, MAP_FAILED, MAP_PRIVATE, PROT_READ, PROT_WRITE};

        vmem::bootstrap();

        let addr = mmap(
            ptr::null_mut(),
            0x40000000,
            PROT_READ | PROT_WRITE,
            MAP_ANON | MAP_PRIVATE,
            0,
            0,
        );
        if addr == MAP_FAILED {
            panic!();
        }

        arena.add(addr as usize, 0x40000000).unwrap();
    }

    arena.log_segment_list();
    let addr = arena.alloc(0x1000, AllocStrategy::InstantFit);
    arena.log_segment_list();
    unsafe { arena.free(addr.unwrap(), 0x1000) };
    arena.log_segment_list();

    let base1 = arena.alloc(0x1000, AllocStrategy::InstantFit).unwrap();
    let base2 = arena.alloc(0x1000, AllocStrategy::InstantFit).unwrap();
    let base3 = arena.alloc(0x1000, AllocStrategy::InstantFit).unwrap();
    let base = arena
        .alloc_constrained(
            vmem::Layout::new(10).align(8).phase(6),
            AllocStrategy::InstantFit,
        )
        .unwrap();

    unsafe {
        arena.log_segment_list();
        arena.free(base2, 0x1000);
        arena.free(base, 10);
        arena.log_segment_list();
        arena.free(base1, 0x1000);
        arena.free(base3, 0x1000);
        arena.log_segment_list();
    }
}
