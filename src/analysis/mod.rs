//!
//!Traits for sets with orderings and metrics
//!
//!Traits in this module have been split into three groups:
//!* ["Ordered"](ordered) sets and related properties. This includes the
//! [archimedian property](ArchimedeanProperty) and ordered algebraic systems.
//!* Traits for [Real](Real) and [Complex](Complex) properties and representations
//!* ["Metric"](metric) properties and functions. This includes
//! [metrics](Metric), [norms](Norm), and [inner-products](InnerProductSpace)
//!
//!For ease of use, members of each module have been re-exported into this one.
//!

pub use self::ordered::*;
pub use self::real::*;
pub use self::metric::*;

pub mod ordered;
pub mod real;
pub mod metric;
