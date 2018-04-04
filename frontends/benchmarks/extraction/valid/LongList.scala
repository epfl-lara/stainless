import stainless.collection._

object LongList {
  case class Level() {
    def l: List[Char] =
      List('o','o','o','-','-','-','-','-','-','-','\n',
           'o','S','o','o','o','o','-','-','-','-','\n',
           'o','o','o','o','o','o','o','o','o','-','\n',
           '-','o','o','o','o','o','o','o','o','o','\n',
           '-','-','-','-','-','o','o','T','o','o','\n',
           '-','-','-','-','-','-','o','o','o','-','\n')
  }
}
