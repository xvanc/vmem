(function() {var implementors = {
"lock_api":[["impl&lt;R, T&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.Mutex.html\" title=\"struct lock_api::Mutex\">Mutex</a>&lt;R, T&gt;",1,["lock_api::mutex::Mutex"]],["impl&lt;'a, R, T&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.MutexGuard.html\" title=\"struct lock_api::MutexGuard\">MutexGuard</a>&lt;'a, R, T&gt;",1,["lock_api::mutex::MutexGuard"]],["impl&lt;'a, R, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.MappedMutexGuard.html\" title=\"struct lock_api::MappedMutexGuard\">MappedMutexGuard</a>&lt;'a, R, T&gt;<span class=\"where fmt-newline\">where\n    R: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a>,\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a>,</span>",1,["lock_api::mutex::MappedMutexGuard"]],["impl&lt;R, G&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.RawReentrantMutex.html\" title=\"struct lock_api::RawReentrantMutex\">RawReentrantMutex</a>&lt;R, G&gt;",1,["lock_api::remutex::RawReentrantMutex"]],["impl&lt;R, G, T&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.ReentrantMutex.html\" title=\"struct lock_api::ReentrantMutex\">ReentrantMutex</a>&lt;R, G, T&gt;",1,["lock_api::remutex::ReentrantMutex"]],["impl&lt;'a, R, G, T&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.ReentrantMutexGuard.html\" title=\"struct lock_api::ReentrantMutexGuard\">ReentrantMutexGuard</a>&lt;'a, R, G, T&gt;",1,["lock_api::remutex::ReentrantMutexGuard"]],["impl&lt;'a, R, G, T&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.MappedReentrantMutexGuard.html\" title=\"struct lock_api::MappedReentrantMutexGuard\">MappedReentrantMutexGuard</a>&lt;'a, R, G, T&gt;",1,["lock_api::remutex::MappedReentrantMutexGuard"]],["impl&lt;R, T&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.RwLock.html\" title=\"struct lock_api::RwLock\">RwLock</a>&lt;R, T&gt;",1,["lock_api::rwlock::RwLock"]],["impl&lt;'a, R, T&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.RwLockReadGuard.html\" title=\"struct lock_api::RwLockReadGuard\">RwLockReadGuard</a>&lt;'a, R, T&gt;",1,["lock_api::rwlock::RwLockReadGuard"]],["impl&lt;'a, R, T&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.RwLockWriteGuard.html\" title=\"struct lock_api::RwLockWriteGuard\">RwLockWriteGuard</a>&lt;'a, R, T&gt;",1,["lock_api::rwlock::RwLockWriteGuard"]],["impl&lt;'a, R, T&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.RwLockUpgradableReadGuard.html\" title=\"struct lock_api::RwLockUpgradableReadGuard\">RwLockUpgradableReadGuard</a>&lt;'a, R, T&gt;",1,["lock_api::rwlock::RwLockUpgradableReadGuard"]],["impl&lt;'a, R, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.MappedRwLockReadGuard.html\" title=\"struct lock_api::MappedRwLockReadGuard\">MappedRwLockReadGuard</a>&lt;'a, R, T&gt;<span class=\"where fmt-newline\">where\n    R: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a>,\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a>,</span>",1,["lock_api::rwlock::MappedRwLockReadGuard"]],["impl&lt;'a, R, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.MappedRwLockWriteGuard.html\" title=\"struct lock_api::MappedRwLockWriteGuard\">MappedRwLockWriteGuard</a>&lt;'a, R, T&gt;<span class=\"where fmt-newline\">where\n    R: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a>,\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a>,</span>",1,["lock_api::rwlock::MappedRwLockWriteGuard"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.GuardSend.html\" title=\"struct lock_api::GuardSend\">GuardSend</a>",1,["lock_api::GuardSend"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"lock_api/struct.GuardNoSend.html\" title=\"struct lock_api::GuardNoSend\">GuardNoSend</a>",1,["lock_api::GuardNoSend"]]],
"log":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"enum\" href=\"log/enum.Level.html\" title=\"enum log::Level\">Level</a>",1,["log::Level"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"enum\" href=\"log/enum.LevelFilter.html\" title=\"enum log::LevelFilter\">LevelFilter</a>",1,["log::LevelFilter"]],["impl&lt;'a&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"log/struct.Record.html\" title=\"struct log::Record\">Record</a>&lt;'a&gt;",1,["log::Record"]],["impl&lt;'a&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"log/struct.RecordBuilder.html\" title=\"struct log::RecordBuilder\">RecordBuilder</a>&lt;'a&gt;",1,["log::RecordBuilder"]],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"log/struct.Metadata.html\" title=\"struct log::Metadata\">Metadata</a>&lt;'a&gt;",1,["log::Metadata"]],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"log/struct.MetadataBuilder.html\" title=\"struct log::MetadataBuilder\">MetadataBuilder</a>&lt;'a&gt;",1,["log::MetadataBuilder"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"log/struct.SetLoggerError.html\" title=\"struct log::SetLoggerError\">SetLoggerError</a>",1,["log::SetLoggerError"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"log/struct.ParseLevelError.html\" title=\"struct log::ParseLevelError\">ParseLevelError</a>",1,["log::ParseLevelError"]]],
"scopeguard":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"enum\" href=\"scopeguard/enum.Always.html\" title=\"enum scopeguard::Always\">Always</a>",1,["scopeguard::Always"]],["impl&lt;T, F, S&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"scopeguard/struct.ScopeGuard.html\" title=\"struct scopeguard::ScopeGuard\">ScopeGuard</a>&lt;T, F, S&gt;<span class=\"where fmt-newline\">where\n    F: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a>,\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a>,</span>",1,["scopeguard::ScopeGuard"]]],
"spin":[["impl&lt;R = <a class=\"struct\" href=\"spin/relax/struct.Spin.html\" title=\"struct spin::relax::Spin\">Spin</a>&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/barrier/struct.Barrier.html\" title=\"struct spin::barrier::Barrier\">Barrier</a>&lt;R&gt;",1,["spin::barrier::Barrier"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/barrier/struct.BarrierWaitResult.html\" title=\"struct spin::barrier::BarrierWaitResult\">BarrierWaitResult</a>",1,["spin::barrier::BarrierWaitResult"]],["impl&lt;T, F = <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.71.1/core/primitive.fn.html\">fn</a>() -&gt; T, R = <a class=\"struct\" href=\"spin/relax/struct.Spin.html\" title=\"struct spin::relax::Spin\">Spin</a>&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/lazy/struct.Lazy.html\" title=\"struct spin::lazy::Lazy\">Lazy</a>&lt;T, F, R&gt;",1,["spin::lazy::Lazy"]],["impl&lt;T, R = <a class=\"struct\" href=\"spin/relax/struct.Spin.html\" title=\"struct spin::relax::Spin\">Spin</a>&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/mutex/spin/struct.SpinMutex.html\" title=\"struct spin::mutex::spin::SpinMutex\">SpinMutex</a>&lt;T, R&gt;",1,["spin::mutex::spin::SpinMutex"]],["impl&lt;'a, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/mutex/spin/struct.SpinMutexGuard.html\" title=\"struct spin::mutex::spin::SpinMutexGuard\">SpinMutexGuard</a>&lt;'a, T&gt;<span class=\"where fmt-newline\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a>,</span>",1,["spin::mutex::spin::SpinMutexGuard"]],["impl&lt;T, R = <a class=\"struct\" href=\"spin/relax/struct.Spin.html\" title=\"struct spin::relax::Spin\">Spin</a>&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/mutex/struct.Mutex.html\" title=\"struct spin::mutex::Mutex\">Mutex</a>&lt;T, R&gt;",1,["spin::mutex::Mutex"]],["impl&lt;'a, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/mutex/struct.MutexGuard.html\" title=\"struct spin::mutex::MutexGuard\">MutexGuard</a>&lt;'a, T&gt;<span class=\"where fmt-newline\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a>,</span>",1,["spin::mutex::MutexGuard"]],["impl&lt;T = <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.71.1/core/primitive.unit.html\">()</a>, R = <a class=\"struct\" href=\"spin/relax/struct.Spin.html\" title=\"struct spin::relax::Spin\">Spin</a>&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/once/struct.Once.html\" title=\"struct spin::once::Once\">Once</a>&lt;T, R&gt;",1,["spin::once::Once"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/relax/struct.Spin.html\" title=\"struct spin::relax::Spin\">Spin</a>",1,["spin::relax::Spin"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/relax/struct.Loop.html\" title=\"struct spin::relax::Loop\">Loop</a>",1,["spin::relax::Loop"]],["impl&lt;T, R = <a class=\"struct\" href=\"spin/relax/struct.Spin.html\" title=\"struct spin::relax::Spin\">Spin</a>&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/rwlock/struct.RwLock.html\" title=\"struct spin::rwlock::RwLock\">RwLock</a>&lt;T, R&gt;",1,["spin::rwlock::RwLock"]],["impl&lt;'a, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/rwlock/struct.RwLockReadGuard.html\" title=\"struct spin::rwlock::RwLockReadGuard\">RwLockReadGuard</a>&lt;'a, T&gt;<span class=\"where fmt-newline\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a>,</span>",1,["spin::rwlock::RwLockReadGuard"]],["impl&lt;'a, T, R = <a class=\"struct\" href=\"spin/relax/struct.Spin.html\" title=\"struct spin::relax::Spin\">Spin</a>&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/rwlock/struct.RwLockWriteGuard.html\" title=\"struct spin::rwlock::RwLockWriteGuard\">RwLockWriteGuard</a>&lt;'a, T, R&gt;",1,["spin::rwlock::RwLockWriteGuard"]],["impl&lt;'a, T, R = <a class=\"struct\" href=\"spin/relax/struct.Spin.html\" title=\"struct spin::relax::Spin\">Spin</a>&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"spin/rwlock/struct.RwLockUpgradableGuard.html\" title=\"struct spin::rwlock::RwLockUpgradableGuard\">RwLockUpgradableGuard</a>&lt;'a, T, R&gt;",1,["spin::rwlock::RwLockUpgradableGuard"]]],
"vmem":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"enum\" href=\"vmem/enum.Error.html\" title=\"enum vmem::Error\">Error</a>",1,["vmem::vmem::Error"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"vmem/struct.Layout.html\" title=\"struct vmem::Layout\">Layout</a>",1,["vmem::vmem::Layout"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"enum\" href=\"vmem/enum.AllocStrategy.html\" title=\"enum vmem::AllocStrategy\">AllocStrategy</a>",1,["vmem::vmem::AllocStrategy"]],["impl&lt;'name, 'src&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/panic/unwind_safe/trait.RefUnwindSafe.html\" title=\"trait core::panic::unwind_safe::RefUnwindSafe\">RefUnwindSafe</a> for <a class=\"struct\" href=\"vmem/struct.Vmem.html\" title=\"struct vmem::Vmem\">Vmem</a>&lt;'name, 'src&gt;",1,["vmem::vmem::Vmem"]]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()