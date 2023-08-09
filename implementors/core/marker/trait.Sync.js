(function() {var implementors = {
"lock_api":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.GuardSend.html\" title=\"struct lock_api::GuardSend\">GuardSend</a>",1,["lock_api::GuardSend"]],["impl&lt;'a, R: <a class=\"trait\" href=\"lock_api/trait.RawMutex.html\" title=\"trait lock_api::RawMutex\">RawMutex</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a, G: <a class=\"trait\" href=\"lock_api/trait.GetThreadId.html\" title=\"trait lock_api::GetThreadId\">GetThreadId</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.MappedReentrantMutexGuard.html\" title=\"struct lock_api::MappedReentrantMutexGuard\">MappedReentrantMutexGuard</a>&lt;'a, R, G, T&gt;"],["impl&lt;R: <a class=\"trait\" href=\"lock_api/trait.RawMutex.html\" title=\"trait lock_api::RawMutex\">RawMutex</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.Mutex.html\" title=\"struct lock_api::Mutex\">Mutex</a>&lt;R, T&gt;"],["impl&lt;'a, R: <a class=\"trait\" href=\"lock_api/trait.RawMutex.html\" title=\"trait lock_api::RawMutex\">RawMutex</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.MappedMutexGuard.html\" title=\"struct lock_api::MappedMutexGuard\">MappedMutexGuard</a>&lt;'a, R, T&gt;"],["impl&lt;'a, R: <a class=\"trait\" href=\"lock_api/trait.RawRwLock.html\" title=\"trait lock_api::RawRwLock\">RawRwLock</a> + 'a, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.MappedRwLockWriteGuard.html\" title=\"struct lock_api::MappedRwLockWriteGuard\">MappedRwLockWriteGuard</a>&lt;'a, R, T&gt;"],["impl&lt;R: <a class=\"trait\" href=\"lock_api/trait.RawMutex.html\" title=\"trait lock_api::RawMutex\">RawMutex</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>, G: <a class=\"trait\" href=\"lock_api/trait.GetThreadId.html\" title=\"trait lock_api::GetThreadId\">GetThreadId</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.ReentrantMutex.html\" title=\"struct lock_api::ReentrantMutex\">ReentrantMutex</a>&lt;R, G, T&gt;"],["impl&lt;R: <a class=\"trait\" href=\"lock_api/trait.RawRwLock.html\" title=\"trait lock_api::RawRwLock\">RawRwLock</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.RwLock.html\" title=\"struct lock_api::RwLock\">RwLock</a>&lt;R, T&gt;"],["impl&lt;R: <a class=\"trait\" href=\"lock_api/trait.RawRwLock.html\" title=\"trait lock_api::RawRwLock\">RawRwLock</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>, T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.RwLockReadGuard.html\" title=\"struct lock_api::RwLockReadGuard\">RwLockReadGuard</a>&lt;'_, R, T&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.GuardNoSend.html\" title=\"struct lock_api::GuardNoSend\">GuardNoSend</a>"],["impl&lt;R: <a class=\"trait\" href=\"lock_api/trait.RawRwLock.html\" title=\"trait lock_api::RawRwLock\">RawRwLock</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>, T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.RwLockWriteGuard.html\" title=\"struct lock_api::RwLockWriteGuard\">RwLockWriteGuard</a>&lt;'_, R, T&gt;"],["impl&lt;'a, R: <a class=\"trait\" href=\"lock_api/trait.RawMutex.html\" title=\"trait lock_api::RawMutex\">RawMutex</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a, G: <a class=\"trait\" href=\"lock_api/trait.GetThreadId.html\" title=\"trait lock_api::GetThreadId\">GetThreadId</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.ReentrantMutexGuard.html\" title=\"struct lock_api::ReentrantMutexGuard\">ReentrantMutexGuard</a>&lt;'a, R, G, T&gt;"],["impl&lt;'a, R: <a class=\"trait\" href=\"lock_api/trait.RawRwLock.html\" title=\"trait lock_api::RawRwLock\">RawRwLock</a> + 'a, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.MappedRwLockReadGuard.html\" title=\"struct lock_api::MappedRwLockReadGuard\">MappedRwLockReadGuard</a>&lt;'a, R, T&gt;"],["impl&lt;R: <a class=\"trait\" href=\"lock_api/trait.RawMutex.html\" title=\"trait lock_api::RawMutex\">RawMutex</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>, G: <a class=\"trait\" href=\"lock_api/trait.GetThreadId.html\" title=\"trait lock_api::GetThreadId\">GetThreadId</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.RawReentrantMutex.html\" title=\"struct lock_api::RawReentrantMutex\">RawReentrantMutex</a>&lt;R, G&gt;"],["impl&lt;'a, R: <a class=\"trait\" href=\"lock_api/trait.RawRwLockUpgrade.html\" title=\"trait lock_api::RawRwLockUpgrade\">RawRwLockUpgrade</a> + 'a, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.RwLockUpgradableReadGuard.html\" title=\"struct lock_api::RwLockUpgradableReadGuard\">RwLockUpgradableReadGuard</a>&lt;'a, R, T&gt;"],["impl&lt;'a, R: <a class=\"trait\" href=\"lock_api/trait.RawMutex.html\" title=\"trait lock_api::RawMutex\">RawMutex</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> + 'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"lock_api/struct.MutexGuard.html\" title=\"struct lock_api::MutexGuard\">MutexGuard</a>&lt;'a, R, T&gt;"]],
"log":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"enum\" href=\"log/enum.Level.html\" title=\"enum log::Level\">Level</a>",1,["log::Level"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"enum\" href=\"log/enum.LevelFilter.html\" title=\"enum log::LevelFilter\">LevelFilter</a>",1,["log::LevelFilter"]],["impl&lt;'a&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"log/struct.Record.html\" title=\"struct log::Record\">Record</a>&lt;'a&gt;",1,["log::Record"]],["impl&lt;'a&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"log/struct.RecordBuilder.html\" title=\"struct log::RecordBuilder\">RecordBuilder</a>&lt;'a&gt;",1,["log::RecordBuilder"]],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"log/struct.Metadata.html\" title=\"struct log::Metadata\">Metadata</a>&lt;'a&gt;",1,["log::Metadata"]],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"log/struct.MetadataBuilder.html\" title=\"struct log::MetadataBuilder\">MetadataBuilder</a>&lt;'a&gt;",1,["log::MetadataBuilder"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"log/struct.SetLoggerError.html\" title=\"struct log::SetLoggerError\">SetLoggerError</a>",1,["log::SetLoggerError"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"log/struct.ParseLevelError.html\" title=\"struct log::ParseLevelError\">ParseLevelError</a>",1,["log::ParseLevelError"]]],
"scopeguard":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"enum\" href=\"scopeguard/enum.Always.html\" title=\"enum scopeguard::Always\">Always</a>",1,["scopeguard::Always"]],["impl&lt;T, F, S&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"scopeguard/struct.ScopeGuard.html\" title=\"struct scopeguard::ScopeGuard\">ScopeGuard</a>&lt;T, F, S&gt;<span class=\"where fmt-newline\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>,\n    F: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/ops/function/trait.FnOnce.html\" title=\"trait core::ops::function::FnOnce\">FnOnce</a>(T),\n    S: <a class=\"trait\" href=\"scopeguard/trait.Strategy.html\" title=\"trait scopeguard::Strategy\">Strategy</a>,</span>"]],
"spin":[["impl&lt;R&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/barrier/struct.Barrier.html\" title=\"struct spin::barrier::Barrier\">Barrier</a>&lt;R&gt;",1,["spin::barrier::Barrier"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/barrier/struct.BarrierWaitResult.html\" title=\"struct spin::barrier::BarrierWaitResult\">BarrierWaitResult</a>",1,["spin::barrier::BarrierWaitResult"]],["impl&lt;T, F = <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.71.1/core/primitive.fn.html\">fn</a>() -&gt; T, R = <a class=\"struct\" href=\"spin/relax/struct.Spin.html\" title=\"struct spin::relax::Spin\">Spin</a>&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/lazy/struct.Lazy.html\" title=\"struct spin::lazy::Lazy\">Lazy</a>&lt;T, F, R&gt;",1,["spin::lazy::Lazy"]],["impl&lt;'a, T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/mutex/struct.MutexGuard.html\" title=\"struct spin::mutex::MutexGuard\">MutexGuard</a>&lt;'a, T&gt;<span class=\"where fmt-newline\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>,</span>",1,["spin::mutex::MutexGuard"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/relax/struct.Spin.html\" title=\"struct spin::relax::Spin\">Spin</a>",1,["spin::relax::Spin"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/relax/struct.Loop.html\" title=\"struct spin::relax::Loop\">Loop</a>",1,["spin::relax::Loop"]],["impl&lt;T, F: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/lazy/struct.Lazy.html\" title=\"struct spin::lazy::Lazy\">Lazy</a>&lt;T, F&gt;<span class=\"where fmt-newline\">where\n    <a class=\"struct\" href=\"spin/once/struct.Once.html\" title=\"struct spin::once::Once\">Once</a>&lt;T&gt;: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>,</span>"],["impl&lt;T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>, R&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/rwlock/struct.RwLockUpgradableGuard.html\" title=\"struct spin::rwlock::RwLockUpgradableGuard\">RwLockUpgradableGuard</a>&lt;'_, T, R&gt;"],["impl&lt;T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/mutex/spin/struct.SpinMutexGuard.html\" title=\"struct spin::mutex::spin::SpinMutexGuard\">SpinMutexGuard</a>&lt;'_, T&gt;"],["impl&lt;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>, R&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/once/struct.Once.html\" title=\"struct spin::once::Once\">Once</a>&lt;T, R&gt;"],["impl&lt;T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a>, R&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/mutex/struct.Mutex.html\" title=\"struct spin::mutex::Mutex\">Mutex</a>&lt;T, R&gt;"],["impl&lt;T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a>, R&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/mutex/spin/struct.SpinMutex.html\" title=\"struct spin::mutex::spin::SpinMutex\">SpinMutex</a>&lt;T, R&gt;"],["impl&lt;T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>, R&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/rwlock/struct.RwLockWriteGuard.html\" title=\"struct spin::rwlock::RwLockWriteGuard\">RwLockWriteGuard</a>&lt;'_, T, R&gt;"],["impl&lt;T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>, R&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/rwlock/struct.RwLock.html\" title=\"struct spin::rwlock::RwLock\">RwLock</a>&lt;T, R&gt;"],["impl&lt;T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"spin/rwlock/struct.RwLockReadGuard.html\" title=\"struct spin::rwlock::RwLockReadGuard\">RwLockReadGuard</a>&lt;'_, T&gt;"]],
"vmem":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"enum\" href=\"vmem/enum.Error.html\" title=\"enum vmem::Error\">Error</a>",1,["vmem::vmem::Error"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"vmem/struct.Layout.html\" title=\"struct vmem::Layout\">Layout</a>",1,["vmem::vmem::Layout"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"enum\" href=\"vmem/enum.AllocStrategy.html\" title=\"enum vmem::AllocStrategy\">AllocStrategy</a>",1,["vmem::vmem::AllocStrategy"]],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.71.1/core/marker/trait.Sync.html\" title=\"trait core::marker::Sync\">Sync</a> for <a class=\"struct\" href=\"vmem/struct.Vmem.html\" title=\"struct vmem::Vmem\">Vmem</a>&lt;'_, '_&gt;"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()