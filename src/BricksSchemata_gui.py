# Form implementation generated from reading ui file 'BricksSchemata_gui.ui'
#
# Created by: PyQt6 UI code generator 6.6.1
#
# WARNING: Any manual changes made to this file will be lost when pyuic6 is
# run again.  Do not edit this file unless you know what you are doing.


from PyQt6 import QtCore, QtGui, QtWidgets


class Ui_MainWindow(object):
    def setupUi(self, MainWindow):
        MainWindow.setObjectName("MainWindow")
        MainWindow.resize(773, 918)
        sizePolicy = QtWidgets.QSizePolicy(QtWidgets.QSizePolicy.Policy.Preferred, QtWidgets.QSizePolicy.Policy.Preferred)
        sizePolicy.setHorizontalStretch(0)
        sizePolicy.setVerticalStretch(0)
        sizePolicy.setHeightForWidth(MainWindow.sizePolicy().hasHeightForWidth())
        MainWindow.setSizePolicy(sizePolicy)
        self.centralwidget = QtWidgets.QWidget(parent=MainWindow)
        self.centralwidget.setObjectName("centralwidget")
        self.horizontalLayoutWidget_2 = QtWidgets.QWidget(parent=self.centralwidget)
        self.horizontalLayoutWidget_2.setGeometry(QtCore.QRect(20, 20, 721, 51))
        self.horizontalLayoutWidget_2.setObjectName("horizontalLayoutWidget_2")
        self.horizontalLayout_2 = QtWidgets.QHBoxLayout(self.horizontalLayoutWidget_2)
        self.horizontalLayout_2.setContentsMargins(0, 0, 0, 0)
        self.horizontalLayout_2.setObjectName("horizontalLayout_2")
        self.LED = QtWidgets.QPushButton(parent=self.horizontalLayoutWidget_2)
        sizePolicy = QtWidgets.QSizePolicy(QtWidgets.QSizePolicy.Policy.Fixed, QtWidgets.QSizePolicy.Policy.Fixed)
        sizePolicy.setHorizontalStretch(20)
        sizePolicy.setVerticalStretch(20)
        sizePolicy.setHeightForWidth(self.LED.sizePolicy().hasHeightForWidth())
        self.LED.setSizePolicy(sizePolicy)
        self.LED.setText("")
        self.LED.setObjectName("LED")
        self.horizontalLayout_2.addWidget(self.LED)
        self.label = QtWidgets.QLabel(parent=self.horizontalLayoutWidget_2)
        font = QtGui.QFont()
        font.setPointSize(20)
        self.label.setFont(font)
        self.label.setObjectName("label")
        self.horizontalLayout_2.addWidget(self.label)
        spacerItem = QtWidgets.QSpacerItem(40, 20, QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Minimum)
        self.horizontalLayout_2.addItem(spacerItem)
        self.labelProject = QtWidgets.QLabel(parent=self.horizontalLayoutWidget_2)
        font = QtGui.QFont()
        font.setPointSize(20)
        font.setBold(True)
        font.setItalic(True)
        font.setWeight(75)
        self.labelProject.setFont(font)
        self.labelProject.setText("")
        self.labelProject.setObjectName("labelProject")
        self.horizontalLayout_2.addWidget(self.labelProject)
        spacerItem1 = QtWidgets.QSpacerItem(40, 20, QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Minimum)
        self.horizontalLayout_2.addItem(spacerItem1)
        self.pushMinimise = QtWidgets.QPushButton(parent=self.horizontalLayoutWidget_2)
        self.pushMinimise.setObjectName("pushMinimise")
        self.horizontalLayout_2.addWidget(self.pushMinimise)
        self.pushMaximise = QtWidgets.QPushButton(parent=self.horizontalLayoutWidget_2)
        self.pushMaximise.setObjectName("pushMaximise")
        self.horizontalLayout_2.addWidget(self.pushMaximise)
        self.pushNormal = QtWidgets.QPushButton(parent=self.horizontalLayoutWidget_2)
        self.pushNormal.setObjectName("pushNormal")
        self.horizontalLayout_2.addWidget(self.pushNormal)
        self.horizontalLayoutWidget_3 = QtWidgets.QWidget(parent=self.centralwidget)
        self.horizontalLayoutWidget_3.setGeometry(QtCore.QRect(20, 84, 721, 71))
        self.horizontalLayoutWidget_3.setObjectName("horizontalLayoutWidget_3")
        self.horizontalLayout_3 = QtWidgets.QHBoxLayout(self.horizontalLayoutWidget_3)
        self.horizontalLayout_3.setContentsMargins(0, 0, 0, 0)
        self.horizontalLayout_3.setObjectName("horizontalLayout_3")
        self.pushOntologyCreate = QtWidgets.QPushButton(parent=self.horizontalLayoutWidget_3)
        self.pushOntologyCreate.setObjectName("pushOntologyCreate")
        self.horizontalLayout_3.addWidget(self.pushOntologyCreate)
        self.pushOntologyLoad = QtWidgets.QPushButton(parent=self.horizontalLayoutWidget_3)
        self.pushOntologyLoad.setObjectName("pushOntologyLoad")
        self.horizontalLayout_3.addWidget(self.pushOntologyLoad)
        self.pushExit = QtWidgets.QPushButton(parent=self.horizontalLayoutWidget_3)
        self.pushExit.setObjectName("pushExit")
        self.horizontalLayout_3.addWidget(self.pushExit)
        spacerItem2 = QtWidgets.QSpacerItem(40, 20, QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Minimum)
        self.horizontalLayout_3.addItem(spacerItem2)
        self.pushTreeVisualise = QtWidgets.QPushButton(parent=self.horizontalLayoutWidget_3)
        self.pushTreeVisualise.setObjectName("pushTreeVisualise")
        self.horizontalLayout_3.addWidget(self.pushTreeVisualise)
        spacerItem3 = QtWidgets.QSpacerItem(40, 20, QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Minimum)
        self.horizontalLayout_3.addItem(spacerItem3)
        self.pushOntologySave = QtWidgets.QPushButton(parent=self.horizontalLayoutWidget_3)
        self.pushOntologySave.setObjectName("pushOntologySave")
        self.horizontalLayout_3.addWidget(self.pushOntologySave)
        self.pushOntologySaveAs = QtWidgets.QPushButton(parent=self.horizontalLayoutWidget_3)
        self.pushOntologySaveAs.setObjectName("pushOntologySaveAs")
        self.horizontalLayout_3.addWidget(self.pushOntologySaveAs)
        self.verticalLayoutWidget_2 = QtWidgets.QWidget(parent=self.centralwidget)
        self.verticalLayoutWidget_2.setGeometry(QtCore.QRect(30, 210, 160, 95))
        self.verticalLayoutWidget_2.setObjectName("verticalLayoutWidget_2")
        self.verticalLayout_2 = QtWidgets.QVBoxLayout(self.verticalLayoutWidget_2)
        self.verticalLayout_2.setContentsMargins(0, 0, 0, 0)
        self.verticalLayout_2.setObjectName("verticalLayout_2")
        self.pushBrickCreate = QtWidgets.QPushButton(parent=self.verticalLayoutWidget_2)
        self.pushBrickCreate.setToolTip("")
        self.pushBrickCreate.setObjectName("pushBrickCreate")
        self.verticalLayout_2.addWidget(self.pushBrickCreate)
        self.pushBrickRemove = QtWidgets.QPushButton(parent=self.verticalLayoutWidget_2)
        self.pushBrickRemove.setToolTip("")
        self.pushBrickRemove.setObjectName("pushBrickRemove")
        self.verticalLayout_2.addWidget(self.pushBrickRemove)
        self.pushBrickRename = QtWidgets.QPushButton(parent=self.verticalLayoutWidget_2)
        self.pushBrickRename.setToolTip("")
        self.pushBrickRename.setObjectName("pushBrickRename")
        self.verticalLayout_2.addWidget(self.pushBrickRename)
        self.listBricks = QtWidgets.QListWidget(parent=self.centralwidget)
        self.listBricks.setGeometry(QtCore.QRect(30, 340, 341, 551))
        self.listBricks.setObjectName("listBricks")
        self.brickTree = QtWidgets.QTreeWidget(parent=self.centralwidget)
        self.brickTree.setGeometry(QtCore.QRect(400, 340, 349, 551))
        self.brickTree.setAutoExpandDelay(1)
        self.brickTree.setColumnCount(0)
        self.brickTree.setObjectName("brickTree")
        self.brickTree.header().setVisible(False)
        self.brickTree.header().setCascadingSectionResizes(False)
        self.gridLayoutWidget = QtWidgets.QWidget(parent=self.centralwidget)
        self.gridLayoutWidget.setGeometry(QtCore.QRect(400, 210, 349, 121))
        self.gridLayoutWidget.setObjectName("gridLayoutWidget")
        self.gridLayout = QtWidgets.QGridLayout(self.gridLayoutWidget)
        self.gridLayout.setContentsMargins(0, 0, 0, 0)
        self.gridLayout.setObjectName("gridLayout")
        self.pushItemAdd = QtWidgets.QPushButton(parent=self.gridLayoutWidget)
        self.pushItemAdd.setToolTip("")
        self.pushItemAdd.setObjectName("pushItemAdd")
        self.gridLayout.addWidget(self.pushItemAdd, 0, 0, 1, 1)
        self.pushItemRemove = QtWidgets.QPushButton(parent=self.gridLayoutWidget)
        self.pushItemRemove.setToolTip("")
        self.pushItemRemove.setObjectName("pushItemRemove")
        self.gridLayout.addWidget(self.pushItemRemove, 1, 0, 1, 1)
        self.pushPrimitiveRemove = QtWidgets.QPushButton(parent=self.gridLayoutWidget)
        self.pushPrimitiveRemove.setToolTip("")
        self.pushPrimitiveRemove.setObjectName("pushPrimitiveRemove")
        self.gridLayout.addWidget(self.pushPrimitiveRemove, 1, 1, 1, 1)
        self.pushItemRename = QtWidgets.QPushButton(parent=self.gridLayoutWidget)
        self.pushItemRename.setToolTip("")
        self.pushItemRename.setObjectName("pushItemRename")
        self.gridLayout.addWidget(self.pushItemRename, 2, 0, 1, 1)
        self.pushPrimitiveAdd = QtWidgets.QPushButton(parent=self.gridLayoutWidget)
        self.pushPrimitiveAdd.setToolTip("")
        self.pushPrimitiveAdd.setObjectName("pushPrimitiveAdd")
        self.gridLayout.addWidget(self.pushPrimitiveAdd, 0, 1, 1, 1)
        self.pushPrimitiveRename = QtWidgets.QPushButton(parent=self.gridLayoutWidget)
        self.pushPrimitiveRename.setToolTip("")
        self.pushPrimitiveRename.setObjectName("pushPrimitiveRename")
        self.gridLayout.addWidget(self.pushPrimitiveRename, 2, 1, 1, 1)
        self.pushPrimitiveChange = QtWidgets.QPushButton(parent=self.gridLayoutWidget)
        self.pushPrimitiveChange.setToolTip("")
        self.pushPrimitiveChange.setObjectName("pushPrimitiveChange")
        self.gridLayout.addWidget(self.pushPrimitiveChange, 3, 1, 1, 1)
        MainWindow.setCentralWidget(self.centralwidget)
        self.statusbar = QtWidgets.QStatusBar(parent=MainWindow)
        self.statusbar.setObjectName("statusbar")
        MainWindow.setStatusBar(self.statusbar)

        self.retranslateUi(MainWindow)
        QtCore.QMetaObject.connectSlotsByName(MainWindow)

    def retranslateUi(self, MainWindow):
        _translate = QtCore.QCoreApplication.translate
        MainWindow.setWindowTitle(_translate("MainWindow", "MainWindow"))
        self.label.setText(_translate("MainWindow", "Ontology Bricks"))
        self.pushMinimise.setText(_translate("MainWindow", "min"))
        self.pushMaximise.setText(_translate("MainWindow", "max"))
        self.pushNormal.setText(_translate("MainWindow", "norm"))
        self.pushOntologyCreate.setText(_translate("MainWindow", "create"))
        self.pushOntologyLoad.setText(_translate("MainWindow", "load"))
        self.pushExit.setText(_translate("MainWindow", "exit"))
        self.pushTreeVisualise.setText(_translate("MainWindow", "visualise"))
        self.pushOntologySave.setText(_translate("MainWindow", "save"))
        self.pushOntologySaveAs.setText(_translate("MainWindow", "save as"))
        self.pushBrickCreate.setText(_translate("MainWindow", "create brick"))
        self.pushBrickRemove.setText(_translate("MainWindow", "remove brick"))
        self.pushBrickRename.setText(_translate("MainWindow", "rename brick"))
        self.pushItemAdd.setText(_translate("MainWindow", "add item"))
        self.pushItemRemove.setText(_translate("MainWindow", "remove item"))
        self.pushPrimitiveRemove.setText(_translate("MainWindow", "remove primitive"))
        self.pushItemRename.setText(_translate("MainWindow", "rename item"))
        self.pushPrimitiveAdd.setText(_translate("MainWindow", "add primitive"))
        self.pushPrimitiveRename.setText(_translate("MainWindow", "rename primitive"))
        self.pushPrimitiveChange.setText(_translate("MainWindow", "change primitive"))
