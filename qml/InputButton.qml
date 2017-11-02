import QtQuick 2.7
import QtQuick.Controls 1.4
import QtQuick.Controls.Styles 1.4

Button {
  property string textDisplayed
  property string textInserted
  textInserted: textDisplayed // jezeli inaczej nie zdefiniowane,
                              // dodaj to co napisane na przycisku
  text: textDisplayed
  //width: text.contentWidth
  onClicked: function() {
    // respektuj pozycje kursora i dodaj nazwe w jego miejscu
    if (input.text.length > 0) {
      var oldpos = input.cursorPosition;
      var parta = input.text.substring(0, input.cursorPosition);
      var partb = input.text.substring(input.cursorPosition, input.text.length);
      input.text = parta + textInserted + partb;
      input.cursorPosition = oldpos+textInserted.length;
    } else {
      input.text += textInserted
    }
  }
  style: ButtonStyle {
    background: Rectangle {
      implicitWidth: text.contentWidth
      implicitHeight: 25
      border.width: control.activeFocus ? 2 : 1
      border.color: "#888"
      radius: 4
      gradient: Gradient {
          GradientStop { position: 0 ; color: control.pressed ? "#ccc" : "#eee" }
          GradientStop { position: 1 ; color: control.pressed ? "#aaa" : "#ccc" }
      }
    }
  }
}
